import ArgumentParser
import Foundation
import Utils

/// A command-line tool that generates XCTest cases for a list of annotated ".hylo" files as part
/// of our build process.
@main
struct GenerateHyloFileTests: ParsableCommand {

  @Option(
    name: [.customShort("o")],
    help: ArgumentHelp("Write output to <file>.", valueName: "output-swift-file"),
    transform: URL.init(fileURLWithPath:))
  var outputURL: URL

  @Option(
    name: [.customShort("n")],
    help: ArgumentHelp("Name of generated test case.", valueName: "XCTestCase name"))
  var testCaseName: String

  @Argument(
    help: "Paths of annotated hylo source files to be tested.",
    transform: URL.init(fileURLWithPath:))
  var hyloSourceFiles: [URL]

  /// Returns the Swift source of the test function for the Hylo program at `source`, which is the
  /// URL of a single source file or the root directory of a module.
  func swiftFunctionTesting(hyloProgramAt source: URL) throws -> String {
    let firstLine = try String(contentsOf: source).prefix { !$0.isNewline }
    let parsed = try firstLine.parsedAsFirstLineOfAnnotatedHyloFileTest()
    let testID = source.deletingPathExtension().lastPathComponent.asSwiftIdentifier

    return parsed.reduce(into: "") { (swiftCode, test) in
      let trailing = test.arguments.reduce(into: "", { (s, a) in s.write(", \(a)") })
      swiftCode += """

          func test_\(test.methodName)_\(testID)() throws {
            try \(test.methodName)(
              \(String(reflecting: source.fileSystemPath)),
              extending: programToExtend!\(trailing))
          }

        """
    }
  }

  func run() throws {
    var output =
      """
      import TestUtils
      import XCTest

      final class \(testCaseName.asSwiftIdentifier): HyloTestCase {

      """

    for f in hyloSourceFiles {
      do {
        output += try swiftFunctionTesting(hyloProgramAt: f)
      } catch let e as FirstLineError {
        try! FileHandle.standardError.write(
          contentsOf: Data("\(f.fileSystemPath):1: error: \(e.details)\n".utf8))
        GenerateHyloFileTests.exit(withError: ExitCode(-1))
      }
    }

    output += "\n}\n"

    try output.write(to: outputURL, atomically: true, encoding: .utf8)
  }

}

extension String {

  /// Returns a valid Swift identifier made by replacing non-identifier characters in `self` with
  /// underscores, and prefixing it with "X" if it happens to begin with a number.
  fileprivate var asSwiftIdentifier: String {
    let r = String(self.map { $0.isNumber || $0.isLetter ? $0 : "_" })
    return (r.first?.isNumber ?? true) ? "X" + r : r
  }

}

extension StringProtocol where Self.SubSequence == Substring {

  /// Interpreting `self` as the first line of an annotated Hylo test file, returns the embedded
  /// test method name and expectation of success.
  fileprivate func parsedAsFirstLineOfAnnotatedHyloFileTest() throws -> [TestDescription] {
    var text = self[...]
    if !text.removeLeading("//- ") {
      throw FirstLineError("first line of annotated test file must begin with '//-'")
    }

    let m = text.removeFirstUntil(it: \.isWhitespace)
    guard let methodName = TestMethod(rawValue: String(m)) else {
      let s = m.isEmpty ? "missing test method name" : "unknown test method '\(m)'"
      throw FirstLineError(s)
    }

    var arguments: [TestArgument] = []
    while !text.isEmpty {
      // Parse a label.
      text.removeFirstWhile(it: \.isWhitespace)
      let l = text.removeFirstUntil(it: { $0 == ":" })
      if l.isEmpty {
        break
      } else if !text.removeLeading(":") {
        throw FirstLineError("missing colon after argument label")
      }

      // Parse a value.
      text.removeFirstWhile(it: \.isWhitespace)
      let v = text.removeFirstUntil(it: \.isWhitespace)
      if v.isEmpty { throw FirstLineError("missing value after '\(l):'") }

      if let a = TestArgument(l, v) {
        arguments.append(a)
      } else {
        throw FirstLineError("invalid argument '\(l): \(v)'")
      }
    }

    var tests = [TestDescription(methodName: methodName, arguments: arguments)]
    if methodName == .compileAndRun {
      tests.append(TestDescription(methodName: .compileAndRunOptimized, arguments: arguments))
    }
    return tests
  }

}

/// The name of a method implementing the logic of a test runner.
private enum TestMethod: String {

  /// Compiles and runs the program.
  case compileAndRun

  /// Compiles and runs the program with optimizations.
  case compileAndRunOptimized

  /// Compiles the program down to LLVM IR.
  case compileToLLVM

  /// Compiles the program down to Hylo IR.
  case lowerToFinishedIR

  /// Parses the program.
  case parse

  /// Type checks the program.
  case typeCheck

}

/// An argument of a test runner.
private struct TestArgument: CustomStringConvertible {

  /// The label of an argument.
  enum Label: String {

    /// The label of an argument specifying the expected outcome of the test.
    case expecting

  }

  /// The label of the argument.
  let label: Label

  /// The value of the argument.
  let value: String

  /// Creates an instance with the given properties or returns `nil` if the argument is invalid.
  init?(_ label: Substring, _ value: Substring) {
    // Validate the label.
    guard let l = Label(rawValue: String(label)) else {
      return nil
    }

    // Validate the value.
    switch l {
    case .expecting:
      if (value != ".success") && (value != ".failure") { return nil }
    }

    self.label = l
    self.value = String(value)
  }

  var description: String { "\(label): \(value)" }

}

/// Information necessary to generate a test case.
private struct TestDescription {

  /// The name of the method implementing the logic of the test runner.
  let methodName: TestMethod

  /// The arguments of the method.
  let arguments: [TestArgument]

}

/// A failure to parse the first line of an annotated Hylo file.
struct FirstLineError: Error {
  /// Creates an instance whose detailed description is `details`.
  init(_ details: String) { self.details = details }

  /// A detailed description of the cause of this failure.
  let details: String
}
