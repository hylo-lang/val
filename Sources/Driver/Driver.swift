import ArgumentParser
import CodeGenLLVM
import Foundation
import FrontEnd
import IR
import StandardLibrary
import SwiftyLLVM
import Utils

public struct Driver: ParsableCommand {

  /// A validation error that includes the command's full help message.
  private struct ValidationErrorWithHelp: Error, CustomStringConvertible {

    var message: String

    init(_ message: String) {
      self.message = message
    }

    var description: String {
      """
      \(message)

      \(Driver.helpMessage())
      """
    }

  }

  /// The type of the output files to generate.
  private enum OutputType: String, ExpressibleByArgument {

    /// AST before type-checking.
    case rawAST = "raw-ast"

    /// Hylo IR before mandatory transformations.
    case rawIR = "raw-ir"

    /// Hylo IR.
    case ir = "ir"

    /// LLVM IR
    case llvm = "llvm"

    /// Intel ASM
    case intelAsm = "intel-asm"

    /// Executable binary.
    case binary = "binary"
  }

  /// The result of a compiler invocation.
  public struct CompilationResult {

    /// The exit status of the compiler.
    public let status: ExitCode

    /// The URL of the output file.
    public let output: URL

    /// The generated diagnostics.
    public let diagnostics: DiagnosticSet

  }

  public static let configuration = CommandConfiguration(commandName: "hc")

  @Flag(
    name: [.customLong("modules")],
    help: "Compile inputs as separate modules.")
  private var compileInputAsModules: Bool = false

  @Flag(
    name: [.customLong("import-builtin")],
    help: "Import the built-in module.")
  private var importBuiltinModule: Bool = false

  @Flag(
    name: [.customLong("freestanding")],
    help:
      """
      Import only the freestanding core of the standard library, omitting any definitions that \
      depend on having an operating system.
      """)
  private var freestanding: Bool = false

  @Flag(
    name: [.customLong("experimental-parallel-typechecking")],
    help: "Parallelize the type checker")
  private var experimentalParallelTypeChecking: Bool = false

  @Flag(
    name: [.customLong("typecheck")],
    help: "Type-check the input file(s).")
  private var typeCheckOnly: Bool = false

  @Flag(
    name: [.customLong("profile-compiler")],
    help: "Profile the compilation time")
  private var profileCompiler: Bool = false

  @Option(
    name: [.customLong("trace-inference")],
    help: ArgumentHelp(
      "Enable tracing of type inference requests at the given line.",
      valueName: "file:line"))
  private var inferenceTracingSite: SourceLine?

  @Option(
    name: [.customLong("show-requirements")],
    help: ArgumentHelp(
      "Log the requirement system of the generic declaration at the given line.",
      valueName: "file:line"))
  private var showRequirementsSite: SourceLine?

  @Option(
    name: [.customLong("emit")],
    help: ArgumentHelp(
      "Emit the specified type output files. From: raw-ast, raw-ir, ir, llvm, intel-asm, binary",
      valueName: "output-type"))
  private var outputType: OutputType = .binary

  @Option(
    name: [.customLong("transform")],
    help: ArgumentHelp(
      "Apply the specify transformations after IR lowering.",
      valueName: "transforms"))
  private var transforms: ModulePassList?

  @Option(
    name: [.customShort("L")],
    help: ArgumentHelp(
      "Add a directory to the library search path.",
      valueName: "directory"))
  private var librarySearchPaths: [String] = []

  @Option(
    name: [.customShort("l")],
    help: ArgumentHelp(
      "Link the generated module(s) to the specified native library.",
      valueName: "name"))
  private var libraries: [String] = []

  @Option(
    name: [.customShort("o")],
    help: ArgumentHelp("Write output to <file>.", valueName: "file"),
    transform: URL.init(fileURLWithPath:))
  private var outputURL: URL?

  @Flag(
    name: [.short, .long],
    help: "Use verbose output.")
  private var verbose: Bool = false

  @Flag(
    name: [.customShort("V"), .long],
    help: "Output the compiler version.")
  private var version: Bool = false

  @Flag(
    name: [.customShort("O")],
    help: "Compile with optimizations.")
  private var optimize: Bool = false

  @Argument(
    transform: URL.init(fileURLWithPath:))
  private var inputs: [URL] = []

  /// Creates a new instance with default options.
  public init() {}

  /// The URL of the current working directory.
  private var currentDirectory: URL {
    URL(fileURLWithPath: FileManager.default.currentDirectoryPath, isDirectory: true)
  }

  /// Compiles `input` with the given command line arguments and returns the compiler's exit
  /// status, the URL of the output file, and any diagnostics.
  ///
  /// - Parameters:
  ///   - input: The URL of a single Hylo source file or the root directory of a Hylo module.
  ///   - options: The compiler's options sans input and output arguments.
  ///   - baseProgram: A program with some or all of the dependencies of the compiler's input,
  ///     which have been compiled with options compatible with `options`. All dependencies are
  ///     loaded from disk if this argument is `nil`
  public static func compileToTemporary(
    _ input: URL, withOptions options: [String], extending baseProgram: TypedProgram? = nil
  ) throws -> CompilationResult {
    // Prepare the driver.
    let output = FileManager.default.makeTemporaryFileURL()
    let cli = try Driver.parse(options + ["-o", output.relativePath, input.relativePath])

    // Execute the command.
    var log = DiagnosticSet()
    try log.capturingErrors { (ds) in
      try cli.executeCommand(extending: baseProgram, reportingDiagnosticsTo: &ds)
    }
    let status = log.containsError ? ExitCode.failure : ExitCode.success
    return .init(status: status, output: output, diagnostics: log)
  }

  /// Executes the command.
  public func run() throws {
    var log = DiagnosticSet()
    let status: ExitCode

    do {
      try log.capturingErrors { (ds) in
        try executeCommand(reportingDiagnosticsTo: &ds)
      }
      status = log.containsError ? ExitCode.failure : ExitCode.success
    } catch let e {
      print("Unexpected error\n")
      Driver.exit(withError: e)
    }

    log.render(
      into: &standardError, style: ProcessInfo.ansiTerminalIsConnected ? .styled : .unstyled)
    Driver.exit(withError: status)
  }

  /// Executes the command, loading modules into `baseProgram` and reporting diagnostics to `log`.
  ///
  /// - Parameters:
  ///   - baseProgram: A program with some or all of the dependencies of the compiler's input,
  ///     which have been compiled with options compatible with the driver's current configuration.
  ///     All dependencies are loaded from disk if this argument is `nil`
  ///   - log: A set of diagnostics that doesn't contain any error.
  public func executeCommand(
    extending baseProgram: TypedProgram? = nil,
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) throws {
    if version {
      standardError.write("\(hcVersion)\n")
      return
    }

    guard !inputs.isEmpty else {
      throw ValidationErrorWithHelp("Missing expected argument '<inputs> ...'")
    }

    if compileInputAsModules {
      fatalError("compilation as modules not yet implemented.")
    }

    let productName = makeProductName(inputs)

    // Pool of measurements for time profiling
    var profiler: ProfilingMeasurements? = profileCompiler ? ProfilingMeasurements() : nil
    defer { profiler?.printProfilingReport() }

    // There's no need to load the standard library under `--emit raw-ast`.
    if outputType == .rawAST {
      var a = AST()
      _ = try a.loadModule(
        productName, parsing: sourceFiles(in: inputs),
        withBuiltinModuleAccess: importBuiltinModule,
        reportingDiagnosticsTo: &log,
        profileWith: profiler)
      try write(a, to: astFile(productName))
      return
    }

    // Type checking

    let dependencies: TypedProgram
    if let p = baseProgram {
      precondition(
        p.ast.compilationConditions.freestanding == freestanding,
        "program to extend has incompatible compilation factors")
      dependencies = p
    } else {
      let a = try (freestanding ? Host.freestandingLibraryAST : Host.hostedLibraryAST).get()
      dependencies = try TypedProgram(
        annotating: ScopedProgram(a), inParallel: experimentalParallelTypeChecking,
        reportingDiagnosticsTo: &log,
        tracingInferenceIf: shouldTraceInference,
        loggingRequirementSystemIf: shouldLogRequirements,
        profileWith: profiler)
    }

    let (program, sourceModule) = try dependencies.loadModule(
      reportingDiagnosticsTo: &log,
      tracingInferenceIf: shouldTraceInference,
      loggingRequirementSystemIf: shouldLogRequirements
    ) { (ast, log, space) in
      try ast.loadModule(
        productName, parsing: sourceFiles(in: inputs), inNodeSpace: space,
        withBuiltinModuleAccess: importBuiltinModule,
        reportingDiagnosticsTo: &log,
        profileWith: profiler)
    }

    if typeCheckOnly { return }

    // IR
    var ir = try lower(program: program, reportingDiagnosticsTo: &log, profileWith: profiler)

    if outputType == .ir || outputType == .rawIR {
      let m = ir.modules[sourceModule]!
      try m.description.write(to: irFile(productName), atomically: true, encoding: .utf8)
      return
    }

    // LLVM

    logVerbose("begin depolymorphization pass.\n")
    ir.depolymorphize(profileWith: profiler)

    logVerbose("create LLVM target machine.\n")
    #if os(Windows)
      let target = try SwiftyLLVM.TargetMachine(for: .host())
    #else
      let target = try SwiftyLLVM.TargetMachine(for: .host(), relocation: .pic)
    #endif

    logVerbose("create LLVM program.\n")
    var llvmProgram = try LLVMProgram(
      ir, mainModule: sourceModule, for: target, profileWith: profiler)

    logVerbose("LLVM mandatory passes.\n")
    llvmProgram.applyMandatoryPasses()

    if optimize {
      logVerbose("LLVM optimization.\n")
      llvmProgram.optimize()
    }

    logVerbose("LLVM processing complete.\n")
    if outputType == .llvm {
      let m = llvmProgram.llvmModules[sourceModule]!
      logVerbose("writing LLVM output.")
      try m.description.write(to: llvmFile(productName), atomically: true, encoding: .utf8)
      return
    }

    // Intel ASM

    if outputType == .intelAsm {
      try llvmProgram.llvmModules[sourceModule]!.write(
        .assembly, for: target, to: intelASMFile(productName).fileSystemPath)
      return
    }

    // Executables

    assert(outputType == .binary)

    let objectDir = try FileManager.default.makeTemporaryDirectory()
    let objectFiles = try llvmProgram.write(.objectFile, to: objectDir)
    let binaryPath = executableOutputPath(default: productName)

    #if os(macOS)
      try makeMacOSExecutable(
        at: binaryPath, linking: objectFiles, diagnostics: &log, profileWith: profiler)
    #elseif os(Linux)
      try makeLinuxExecutable(
        at: binaryPath, linking: objectFiles, diagnostics: &log, profileWith: profiler)
    #elseif os(Windows)
      try makeWindowsExecutable(
        at: binaryPath, linking: objectFiles, diagnostics: &log, profileWith: profiler)
    #else
      _ = (objectFiles, binaryPath)
      UNIMPLEMENTED()
    #endif
  }

  /// Logs `m` to the standard error iff `verbose` is `true`.
  private func logVerbose(_ m: @autoclosure () -> String) {
    if verbose { standardError.write(m()) }
  }

  /// Returns `true` if type inference related to `n`, which is in `p`, would be traced.
  private func shouldTraceInference(_ n: AnyNodeID, _ p: TypedProgram) -> Bool {
    if let s = inferenceTracingSite {
      return s.bounds.contains(p[n].site.start)
    } else {
      return false
    }
  }

  /// Returns `true` if the requirement system of `n`, which is in `p`, should be logged.
  private func shouldLogRequirements(_ n: AnyDeclID, _ p: TypedProgram) -> Bool {
    if let s = showRequirementsSite {
      return (n.kind.value is GenericDecl.Type) && s.bounds.contains(p[n].site.start)
    } else {
      return false
    }
  }

  /// Returns `program` lowered to Hylo IR, accumulating diagnostics in `log` and throwing if an
  /// error occurred.
  ///
  /// Mandatory IR passes are applied unless `self.outputType` is `.rawIR`.
  private func lower(
    program: TypedProgram, reportingDiagnosticsTo log: inout DiagnosticSet,
    profileWith profiler: ProfilingMeasurements?
  ) throws -> IR.Program {
    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.IRLowering)
    defer { probe?.stop() }
    var loweredModules: [ModuleDecl.ID: IR.Module] = [:]
    for d in program.ast.modules {
      loweredModules[d] = try lower(d, in: program, reportingDiagnosticsTo: &log)
    }

    var ir = IR.Program(syntax: program, modules: loweredModules)
    if let t = transforms {
      for p in t.elements { ir.applyPass(p) }
    }
    return ir
  }

  /// Returns `m`, which is `program`, lowered to Hylo IR, accumulating diagnostics in `log` and
  /// throwing if an error occurred.
  ///
  /// Mandatory IR passes are applied unless `self.outputType` is `.rawIR`.
  private func lower(
    _ m: ModuleDecl.ID, in program: TypedProgram, reportingDiagnosticsTo log: inout DiagnosticSet
  ) throws -> IR.Module {
    var ir = try IR.Module(lowering: m, in: program, reportingDiagnosticsTo: &log)
    if outputType != .rawIR {
      try ir.applyMandatoryPasses(reportingDiagnosticsTo: &log)
    }
    return ir
  }

  /// Combines the object files located at `objects` into an executable file at `binaryPath`,
  /// logging diagnostics to `log`.
  private func makeMacOSExecutable(
    at binaryPath: String, linking objects: [URL], diagnostics: inout DiagnosticSet,
    profileWith profiler: ProfilingMeasurements?
  ) throws {
    let xcrun = try findExecutable(invokedAs: "xcrun").fileSystemPath

    // linking profiling probe
    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.LinkPhase)
    defer { probe?.stop() }

    let sdk =
      try runCommandLine(xcrun, ["--sdk", "macosx", "--show-sdk-path"], diagnostics: &diagnostics)
      ?? ""

    var arguments = [
      "-r", "ld", "-o", binaryPath,
      "-L\(sdk)/usr/lib",
    ]
    arguments.append(contentsOf: librarySearchPaths.map({ "-L\($0)" }))
    arguments.append(contentsOf: objects.map(\.fileSystemPath))
    arguments.append("-lSystem")
    arguments.append(contentsOf: libraries.map({ "-l\($0)" }))

    try runCommandLine(xcrun, arguments, diagnostics: &diagnostics)
  }

  /// Combines the object files located at `objects` into an executable file at `binaryPath`,
  /// logging diagnostics to `log`.
  private func makeLinuxExecutable(
    at binaryPath: String,
    linking objects: [URL],
    diagnostics: inout DiagnosticSet,
    profileWith profiler: ProfilingMeasurements?
  ) throws {
    var arguments = [
      "-o", binaryPath,
    ]
    arguments.append(contentsOf: librarySearchPaths.map({ "-L\($0)" }))
    arguments.append(contentsOf: objects.map(\.fileSystemPath))
    arguments.append(contentsOf: libraries.map({ "-l\($0)" }))

    // linking profiling probe
    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.LinkPhase)
    defer { probe?.stop() }

    // Note: We use "clang" rather than "ld" so that to deal with the entry point of the program.
    // See https://stackoverflow.com/questions/51677440
    try runCommandLine(
      findExecutable(invokedAs: "clang++").fileSystemPath, arguments, diagnostics: &diagnostics)
  }

  /// Combines the object files located at `objects` into an executable file at `binaryPath`,
  /// logging diagnostics to `log`.
  private func makeWindowsExecutable(
    at binaryPath: String,
    linking objects: [URL],
    diagnostics: inout DiagnosticSet,
    profileWith profiler: ProfilingMeasurements?
  ) throws {
    // linking profiling probe
    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.LinkPhase)
    defer { probe?.stop() }

    try runCommandLine(
      findExecutable(invokedAs: "lld-link").fileSystemPath,
      ["-defaultlib:HyloLibC", "-defaultlib:msvcrt", "-out:" + binaryPath]
        + objects.map(\.fileSystemPath),
      diagnostics: &diagnostics)
  }

  /// Returns `self.outputURL` transformed as a suitable executable file path, using `productName`
  /// as a default name if `outputURL` is `nil`.
  private func executableOutputPath(default productName: String) -> String {
    var binaryPath = outputURL?.path ?? URL(fileURLWithPath: productName).fileSystemPath
    if !binaryPath.hasSuffix(Host.executableSuffix) {
      binaryPath += Host.executableSuffix
    }
    return binaryPath
  }

  /// If `inputs` contains a single URL `u` whose path is non-empty, returns the last component of
  /// `u` without any path extension and stripping all leading dots; returns "Main" otherwise.
  private func makeProductName(_ inputs: [URL]) -> String {
    if let u = inputs.uniqueElement {
      let n = u.deletingPathExtension().lastPathComponent.drop(while: { $0 == "." })
      if !n.isEmpty { return String(n) }
    }
    return "Main"
  }

  /// Writes `source` to `url`, possibly with verbose logging.
  private func write(_ source: String, toURL url: URL) throws {
    logVerbose("Writing \(url)")
    try source.write(to: url, atomically: true, encoding: .utf8)
  }

  /// Creates a module from the contents at `url` and adds it to the AST.
  ///
  /// - Requires: `url` must denote a directly.
  private func addModule(url: URL) {
    UNIMPLEMENTED()
  }

  /// Returns the path of the binary executable that is invoked at the command-line with the name
  /// given by `invocationName`.
  private func findExecutable(invokedAs invocationName: String) throws -> URL {
    if let cached = Driver.executableLocationCache[invocationName] { return cached }

    let executableFileName =
      invocationName.hasSuffix(Host.executableSuffix)
      ? invocationName : invocationName + Host.executableSuffix

    // Search in the PATH.
    let path = ProcessInfo.processInfo.environment[Host.pathEnvironmentVariable] ?? ""
    for root in path.split(separator: Host.pathEnvironmentSeparator) {
      let candidate = URL(fileURLWithPath: String(root)).appendingPathComponent(executableFileName)
      if FileManager.default.fileExists(atPath: candidate.fileSystemPath) {
        Driver.executableLocationCache[invocationName] = candidate
        return candidate
      }
    }

    throw EnvironmentError("not found: executable invoked as \(invocationName)")
  }

  /// Runs the executable at `path`, passing `arguments` on the command line, and returns its
  /// standard output sans any leading or trailing whitespace.
  @discardableResult
  private func runCommandLine(
    _ programPath: String,
    _ arguments: [String] = [],
    diagnostics: inout DiagnosticSet
  ) throws -> String? {
    logVerbose(([programPath] + arguments).joined(separator: " "))
    let r = try Process.run(URL(fileURLWithPath: programPath), arguments: arguments)
    return r.standardOutput[].trimmingCharacters(in: .whitespacesAndNewlines)
  }

  /// A map from the name by which an executable is invoked to path of the named binary.
  private static var executableLocationCache: [String: URL] = [:]

  /// Writes a textual description of `input` to the given `output` file.
  func write(_ input: AST, to output: URL) throws {
    let encoder = JSONEncoder().forAST
    try encoder.encode(input).write(to: output, options: .atomic)
  }

  /// Given the desired name of the compiler's product, returns the file to write when "raw-ast" is
  /// selected as the output type.
  private func astFile(_ productName: String) -> URL {
    outputURL ?? URL(fileURLWithPath: productName + ".ast.json")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "ir" or
  /// "raw-ir" is selected as the output type.
  private func irFile(_ productName: String) -> URL {
    outputURL ?? URL(fileURLWithPath: productName + ".ir")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "llvm" is
  /// selected as the output type.
  private func llvmFile(_ productName: String) -> URL {
    outputURL ?? URL(fileURLWithPath: productName + ".ll")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "intel-asm"
  /// is selected as the output type.
  private func intelASMFile(_ productName: String) -> URL {
    outputURL ?? URL(fileURLWithPath: productName + ".s")
  }

  /// Given the desired name of the compiler's product, returns the file to write when "binary" is
  /// selected as the output type.
  private func binaryFile(_ productName: String) -> URL {
    outputURL ?? URL(fileURLWithPath: productName)
  }

}
