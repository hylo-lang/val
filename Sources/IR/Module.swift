import Foundation
import FrontEnd
import OrderedCollections
import Utils

/// A module lowered to Hylo IR.
///
/// A lowered module is a collection of IR functions and a collection of constant IR values, which
/// represent nominal types, traits, and global bindings. These entities may not necessarily have
/// a definition. When they don't, they denote a declaration known to be defined in another module.
public struct Module {

  /// Unique identifier of a module within a program.
  public typealias ID = ModuleDecl.ID

  /// The program defining the functions in `self`.
  public let program: TypedProgram

  /// The module's identifier.
  public let id: ID

  /// The def-use chains of the values in this module.
  public private(set) var uses: [Operand: [Use]] = [:]

  /// The nominal product types defined in the module.
  public private(set) var productTypes: [ProductType] = []

  /// The traits defined in the module.
  public private(set) var traits: [TraitType] = []

  /// The static allocations defined in the module.
  public private(set) var allocations: [StaticStorage] = []

  /// The functions in the module.
  public private(set) var functions: [Function.ID: Function] = [:]

  /// The module's entry function, if any.
  ///
  /// An entry function is the lowered form of a program's entry point, that is the `main` function
  /// of a Hylo program. A module with an entry function is called an entry module. There can be
  /// only one entry module in a program.
  public private(set) var entryFunction: Function.ID?

  /// Creates an instance lowering `m` in `p`, reporting errors and warnings to `log`.
  ///
  /// - Requires: `m` is a valid ID in `p`.
  /// - Throws: `Diagnostics` if lowering fails.
  public init(
    lowering m: ModuleDecl.ID, in p: TypedProgram,
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) throws {
    self.program = p
    self.id = m

    Emitter.withInstance(insertingIn: &self, reportingDiagnosticsTo: &log) { (e) in
      e.incorporateTopLevelDeclarations()
    }
    try log.throwOnError()
  }

  /// The module's name.
  public var name: String {
    program.ast[id].baseName
  }

  /// Accesses the given function.
  public subscript(f: Function.ID) -> Function {
    _read { yield functions[f]! }
    _modify { yield &functions[f]! }
  }

  /// Accesses the given block.
  public subscript(b: Block.ID) -> Block {
    _read { yield functions[b.function]!.blocks[b.address] }
    _modify { yield &functions[b.function]![b.address] }
  }

  /// Accesses the given instruction.
  public subscript(i: InstructionID) -> Instruction {
    _read { yield functions[i.function]!.blocks[i.block].instructions[i.address] }
    _modify { yield &functions[i.function]![i.block].instructions[i.address] }
  }

  /// Accesses the instruction denoted by `o` if it is `.register`; returns `nil` otherwise.
  public subscript(o: Operand) -> Instruction? {
    if case .register(let i) = o {
      return self[i]
    } else {
      return nil
    }
  }

  /// Returns the type of `operand`.
  public func type(of operand: Operand) -> IR.`Type` {
    switch operand {
    case .register(let i):
      return functions[i.function]![i.block][i.address].result!
    case .parameter(let b, let n):
      return functions[b.function]![b.address].inputs[n]
    case .constant(let c):
      return c.type
    }
  }

  /// Returns `true` iff cannot be used to modify or update a value.
  public func isBoundImmutably(_ p: Operand) -> Bool {
    switch p {
    case .parameter(let e, let i):
      let f = e.function
      return (entry(of: f) == e) && (passingConvention(parameter: i, of: f) == .let)
    case .constant:
      return false
    case .register(let i):
      return isBoundImmutably(register: i)
    }
  }

  /// Returns `true` iff the result of `i` cannot be used to modify or update a value.
  public func isBoundImmutably(register i: InstructionID) -> Bool {
    switch self[i] {
    case is AllocStack:
      return false
    case let s as AdvancedByBytes:
      return isBoundImmutably(s.base)
    case let s as Access:
      return isBoundImmutably(s.source)
    case let s as OpenCapture:
      return s.isAccess(.let)
    case is OpenUnion:
      return false
    case let s as PointerToAddress:
      return s.isAccess(.let)
    case let s as Project:
      return s.projection.access == .let
    case let s as SubfieldView:
      return isBoundImmutably(s.recordAddress)
    case let s as WrapExistentialAddr:
      return isBoundImmutably(s.witness)
    default:
      return true
    }
  }

  /// If `p` is a function parameter, returns its passing convention. Otherwise, returns `nil`.
  public func passingConvention(of p: Operand) -> AccessEffect? {
    if case .parameter(let e, let i) = p, entry(of: e.function) == e {
      return passingConvention(parameter: i, of: e.function)
    } else {
      return nil
    }
  }

  /// Returns the passing convention of the `i`-th parameter of `f`.
  public func passingConvention(parameter i: Int, of f: Function.ID) -> AccessEffect {
    // The last parameter of a function denotes its return value.
    let ps = self[f].inputs
    return (i == ps.count) ? .set : ps[i].type.access
  }

  /// Returns the scope in which `i` is used.
  public func scope(containing i: InstructionID) -> AnyScopeID {
    functions[i.function]![i.block].scope
  }

  /// Returns the IDs of the blocks in `f`.
  ///
  /// The first element of the returned collection is the function's entry; other elements are in
  /// no particular order.
  public func blocks(
    in f: Function.ID
  ) -> LazyMapSequence<Function.Blocks.Indices, Block.ID> {
    self[f].blocks.indices.lazy.map({ .init(f, $0.address) })
  }

  /// Returns the IDs of the instructions in `b`, in order.
  public func instructions(
    in b: Block.ID
  ) -> LazyMapSequence<Block.Instructions.Indices, InstructionID> {
    self[b].instructions.indices.lazy.map({ .init(b.function, b.address, $0.address) })
  }

  /// Returns the ID the instruction before `i`.
  func instruction(before i: InstructionID) -> InstructionID? {
    functions[i.function]![i.block].instructions.address(before: i.address)
      .map({ InstructionID(i.function, i.block, $0) })
  }

  /// Returns the ID the instruction after `i`.
  func instruction(after i: InstructionID) -> InstructionID? {
    functions[i.function]![i.block].instructions.address(after: i.address)
      .map({ InstructionID(i.function, i.block, $0) })
  }

  /// Returns the global identity of `block`'s terminator, if it exists.
  func terminator(of block: Block.ID) -> InstructionID? {
    if let a = functions[block.function]!.blocks[block.address].instructions.lastAddress {
      return InstructionID(block, a)
    } else {
      return nil
    }
  }

  /// Returns the register asssigned by `i`, if any.
  func result(of i: InstructionID) -> Operand? {
    if self[i].result != nil {
      return .register(i)
    } else {
      return nil
    }
  }

  /// Returns `true` iff `lhs` is sequenced before `rhs`.
  func dominates(_ lhs: InstructionID, _ rhs: InstructionID) -> Bool {
    if lhs.function != rhs.function { return false }

    // Fast path: both instructions are in the same block.
    if lhs.block == rhs.block {
      let sequence = functions[lhs.function]![lhs.block].instructions
      return lhs.address.precedes(rhs.address, in: sequence)
    }

    // Slow path: use the dominator tree.
    let d = DominatorTree(function: lhs.function, cfg: self[lhs.function].cfg(), in: self)
    return d.dominates(lhs.block, rhs.block)
  }

  /// Returns `true` if `i` is a deinitializer.
  public func isDeinit(_ i: Function.ID) -> Bool {
    switch i.value {
    case .lowered(let d):
      return FunctionDecl.ID(d).map({ (n) in program.ast[n].isDeinit }) ?? false
    case .existentialized(let j):
      return isDeinit(j)
    case .monomorphized(let j, arguments: _):
      return isDeinit(j)
    case .synthesized(let d):
      return d.kind == .deinitialize
    }
  }

  /// Returns whether the IR in `self` is well-formed.
  ///
  /// Use this method as a sanity check to verify the module's invariants.
  public func isWellFormed() -> Bool {
    for f in functions.keys {
      if !isWellFormed(function: f) { return false }
    }
    return true
  }

  /// Returns whether `f` is well-formed.
  ///
  /// Use this method as a sanity check to verify the function's invariants.
  public func isWellFormed(function f: Function.ID) -> Bool {
    return true
  }

  /// Applies all mandatory passes in this module, accumulating diagnostics in `log` and throwing
  /// if a pass reports an error.
  public mutating func applyMandatoryPasses(
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) throws {
    // We only go over user implementations. Synthesized functions are assumed well-formed.
    let work = functions.compactMap({ (f, i) in !(f.isSynthesized || i.entry == nil) ? f : nil })
    func run(_ pass: (Function.ID) -> Void) throws {
      for f in work { pass(f) }
      try log.throwOnError()
    }

    try run({ removeDeadCode(in: $0, diagnostics: &log) })
    try run({ reifyCallsToBundles(in: $0, diagnostics: &log) })
    try run({ reifyAccesses(in: $0, diagnostics: &log) })
    try run({ simplify($0) })
    try run({ closeBorrows(in: $0, diagnostics: &log) })
    try run({ normalizeObjectStates(in: $0, diagnostics: &log) })
    try run({ ensureExclusivity(in: $0, diagnostics: &log) })

    try generateSyntheticImplementations(reportingDiagnosticsTo: &log)
  }

  /// Inserts the IR for the synthesized declarations defined in this module, reporting diagnostics
  /// to `log` and throwing if a an error occurred.
  private mutating func generateSyntheticImplementations(
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) throws {
    Emitter.withInstance(insertingIn: &self, reportingDiagnosticsTo: &log) { (e) in
      e.incorporateSyntheticDeclarations()
    }
    try log.throwOnError()
  }

  /// Adds `t` to the set of nominal product types defined in `self`.
  mutating func addProductType(_ t: ProductType) {
    productTypes.append(t)
  }

  /// Adds `t` to the set of traits defined in `self`.
  mutating func addTrait(_ t: TraitType) {
    traits.append(t)
  }

  /// Adds `d` to the set of static allocations in `self`.
  mutating func addStaticStorage(_ s: StaticStorage) {
    allocations.append(s)
  }

  /// Assigns `identity` to `value` in `self`.
  ///
  /// - Requires: `identity` is not already assigned.
  mutating func addFunction(_ value: Function, for identity: Function.ID) {
    modify(&functions[identity]) { (f) in
      precondition(f == nil)
      f = value
    }
  }

  /// Returns the identity of the IR function corresponding to `i`.
  mutating func demandDeclaration(lowering i: FrontEnd.Conformance.Implementation) -> Function.ID {
    switch i {
    case .explicit(let d):
      return demandDeclaration(lowering: d)!
    case .synthetic(let d):
      return demandDeclaration(lowering: d)
    }
  }

  /// Returns the identity of the IR function corresponding to `d`, or `nil` if `d` can't be
  /// lowered to an IR function.
  mutating func demandDeclaration(lowering d: AnyDeclID) -> Function.ID? {
    switch d.kind {
    case FunctionDecl.self:
      return demandDeclaration(lowering: FunctionDecl.ID(d)!)
    case MethodImpl.self:
      return demandDeclaration(lowering: MethodImpl.ID(d)!)
    case InitializerDecl.self:
      return demandDeclaration(lowering: InitializerDecl.ID(d)!)
    case SubscriptImpl.self:
      return demandDeclaration(lowering: SubscriptImpl.ID(d)!)
    default:
      return nil
    }
  }

  /// Returns the identity of the IR function corresponding to `d`.
  mutating func demandDeclaration(lowering d: FunctionDecl.ID) -> Function.ID {
    let f = Function.ID(d)
    if functions[f] != nil { return f }

    let parameters = program.accumulatedGenericParameters(in: d)
    let output = program.canonical(
      (program[d].type.base as! CallableType).output, in: program[d].scope)
    let inputs = loweredParameters(of: d)

    // External functions have external linkage at the IR level.
    let linkage: Linkage = (program.isExported(d) || program[d].isExternal) ? .external : .module

    let entity = Function(
      isSubscript: false,
      site: program.ast[d].site,
      linkage: linkage,
      genericParameters: Array(parameters),
      inputs: inputs,
      output: output,
      blocks: [])
    addFunction(entity, for: f)

    // Determine if the new function is the module's entry.
    if program.isModuleEntry(d) {
      assert(entryFunction == nil)
      entryFunction = f
    }

    return f
  }

  /// Returns the identity of the IR function corresponding to `d`.
  mutating func demandDeclaration(lowering d: MethodImpl.ID) -> Function.ID {
    let f = Function.ID(d)
    if functions[f] != nil { return f }

    let parameters = program.accumulatedGenericParameters(in: d)
    let output = program.canonical(
      (program[d].type.base as! CallableType).output, in: program[d].scope)
    let inputs = loweredParameters(of: d)

    let entity = Function(
      isSubscript: false,
      site: program.ast[d].site,
      linkage: program.isExported(d) ? .external : .module,
      genericParameters: Array(parameters),
      inputs: inputs,
      output: output,
      blocks: [])
    addFunction(entity, for: f)
    return f
  }

  /// Returns the identity of the IR function corresponding to `d`.
  mutating func demandDeclaration(lowering d: SubscriptImpl.ID) -> Function.ID {
    let f = Function.ID(d)
    if functions[f] != nil { return f }

    let parameters = program.accumulatedGenericParameters(in: d)
    let output = program.canonical(
      SubscriptImplType(program[d].type)!.output, in: program[d].scope)
    let inputs = loweredParameters(of: d)

    let entity = Function(
      isSubscript: true,
      site: program.ast[d].site,
      linkage: program.isExported(d) ? .external : .module,
      genericParameters: Array(parameters),
      inputs: inputs,
      output: output,
      blocks: [])
    addFunction(entity, for: f)
    return f
  }

  /// Returns the identifier of the IR initializer corresponding to `d`.
  mutating func demandDeclaration(lowering d: InitializerDecl.ID) -> Function.ID {
    precondition(!program.ast[d].isMemberwise)

    let f = Function.ID(d)
    if functions[f] != nil { return f }

    let parameters = program.accumulatedGenericParameters(in: d)
    let inputs = loweredParameters(of: d)

    let entity = Function(
      isSubscript: false,
      site: program.ast[d].introducer.site,
      linkage: program.isExported(d) ? .external : .module,
      genericParameters: Array(parameters),
      inputs: inputs,
      output: .void,
      blocks: [])
    addFunction(entity, for: f)
    return f
  }

  /// Returns the identity of the IR function corresponding to `d`.
  mutating func demandDeclaration(lowering d: SynthesizedFunctionDecl) -> Function.ID {
    let f = Function.ID(d)
    if functions[f] != nil { return f }

    let output = program.canonical(d.type.output, in: d.scope)
    var inputs: [Parameter] = []
    appendCaptures(
      d.type.captures, passed: d.type.receiverEffect, to: &inputs, canonicalizedIn: d.scope)
    appendParameters(d.type.inputs, to: &inputs, canonicalizedIn: d.scope)

    let entity = Function(
      isSubscript: false,
      site: .empty(at: program.ast[id].site.start),
      linkage: .external,
      genericParameters: d.genericParameters,
      inputs: inputs,
      output: output,
      blocks: [])
    addFunction(entity, for: f)

    // Determine if the new function is defined in this module.
    if program.module(containing: d.scope) == id {
      var log = DiagnosticSet()
      Emitter.withInstance(insertingIn: &self, reportingDiagnosticsTo: &log) { (emitter) in
        emitter.lower(synthetic: d)
      }
      assert(log.isEmpty, "unexpected diagnostic in synthesized declaration")
    }

    return f
  }

  /// Returns the implementation of the requirement named `r` in `witness`.
  ///
  /// - Requires: `r` identifies a function or subscript requirement in the trait for which
  ///   `witness` has been established.
  mutating func demandImplementation<T: Decl>(
    of r: T.ID, for witness: FrontEnd.Conformance
  ) -> Function.ID {
    demandDeclaration(lowering: witness.implementations[r]!)
  }

  /// Returns the IR function implementing the deinitializer defined in `c`.
  mutating func demandDeinitDeclaration(
    from c: FrontEnd.Conformance
  ) -> Function.ID {
    let d = program.ast.core.deinitializable.deinitialize
    return demandDeclaration(lowering: c.implementations[d]!)
  }

  /// Returns the IR function implementing the `k` variant move-operation defined by
  /// `conformanceToMovable`.
  ///
  /// - Parameters:
  ///   - k: The semantics of a move operation. It must be either `.set` or `.inout`.
  ///   - conformanceToMovable: A conformance to `Movable`.
  mutating func demandTakeValueDeclaration(
    _ k: AccessEffect, definedBy conformanceToMovable: FrontEnd.Conformance
  ) -> Function.ID {
    switch k {
    case .set:
      let d = program.ast.core.movable.moveInitialize
      return demandDeclaration(lowering: conformanceToMovable.implementations[d]!)
    case .inout:
      let d = program.ast.core.movable.moveAssign
      return demandDeclaration(lowering: conformanceToMovable.implementations[d]!)
    default:
      preconditionFailure()
    }
  }

  /// Returns the IR function implementing the copy operation defined in `conformanceToCopyable`.
  ///
  /// - Parameter conformanceToCopyable: A conformance to `Copyable`.
  mutating func demandCopyDeclaration(
    definedBy conformanceToCopyable: FrontEnd.Conformance
  ) -> Function.ID {
    let d = program.ast.core.copyable.copy
    return demandDeclaration(lowering: conformanceToCopyable.implementations[d]!)
  }

  /// Returns the IR function implementing the operator defined in `conformanceToEquatable`.
  ///
  /// - Parameter conformanceToEquatable: A conformance to `Equatable`.
  mutating func demandEqualDeclaration(
    definedBy conformanceToEquatable: FrontEnd.Conformance
  ) -> Function.ID {
    let d = program.ast.core.equatable.equal
    return demandDeclaration(lowering: conformanceToEquatable.implementations[d]!)
  }

  /// Returns a function reference to the implementation of the requirement `r` in `witness`.
  ///
  /// - Requires: `r` identifies a function or subscript requirement in the trait for which
  ///   `witness` has been established.
  mutating func reference<T: Decl>(
    toImplementationOf r: T.ID, for witness: FrontEnd.Conformance
  ) -> FunctionReference {
    let d = demandImplementation(of: r, for: witness)
    return reference(to: d, implementedFor: witness)
  }

  /// Returns a function reference to `d`, which is an implementation that's part of `witness`.
  func reference(
    to d: Function.ID, implementedFor witness: FrontEnd.Conformance
  ) -> FunctionReference {
    var a = witness.arguments
    if let m = program.traitMember(referredBy: d) {
      let r = program[m.trait.decl].receiver.id
      assert(a[r] == nil)
      a[r] = .type(witness.model)
    }
    return FunctionReference(to: d, in: self, specializedBy: a, in: witness.scope)
  }

  /// Returns a member reference to `d`, which is member of `receiver` accessed with capabilities
  /// `k`, specializing `d`'s type for `a` in `scopeOfUse`.
  mutating func memberCallee(
    referringTo d: AnyDeclID, memberOf receiver: AnyType, accessedWith k: AccessEffectSet,
    specializedBy a: GenericArguments, usedIn scopeOfUse: AnyScopeID
  ) -> Callee {
    // Check if `d`'s implementation is synthetic.
    if program.isRequirement(d) && !receiver.isSkolem {
      let t = program.traitDeclaring(d)!
      let c = program.conformance(of: receiver, to: t, exposedTo: scopeOfUse)!
      let f = demandDeclaration(lowering: c.implementations[d]!)
      return .direct(FunctionReference(to: f, in: self, specializedBy: a, in: scopeOfUse))
    } else if let m = MethodDecl.ID(d) {
      return .bundle(BundleReference(to: m, specializedBy: a, requesting: k))
    } else {
      return .direct(FunctionReference(to: d, in: &self, specializedBy: a, in: scopeOfUse))
    }
  }

  /// Returns the lowered declarations of `d`'s parameters.
  private func loweredParameters(of d: FunctionDecl.ID) -> [Parameter] {
    let declType = ArrowType(program[d].type)!
    let captures = declType.captures.lazy.map { (e) in
      program.canonical(e.type, in: program[d].scope)
    }

    var result: [Parameter] = zip(program.captures(of: d), captures).map({ (c, e) in
      if let t = RemoteType(e) {
        return Parameter(decl: c, type: ParameterType(t))
      } else {
        return Parameter(decl: c, type: ParameterType(declType.receiverEffect, e))
      }
    })

    result.append(contentsOf: program.ast[d].parameters.map(pairedWithLoweredType(parameter:)))
    return result
  }

  /// Returns the lowered declarations of `d`'s parameters.
  private func loweredParameters(of d: MethodImpl.ID) -> [Parameter] {
    let bundle = MethodDecl.ID(program[d].scope)!
    let inputs = program.ast[bundle].parameters
    let r = Parameter(AnyDeclID(program[d].receiver), capturedAs: program[d].receiver.type)
    return [r] + inputs.map(pairedWithLoweredType(parameter:))
  }

  /// Returns the lowered declarations of `d`'s parameters.
  ///
  /// `d`'s receiver comes first and is followed by `d`'s formal parameters, from left to right.
  private func loweredParameters(of d: InitializerDecl.ID) -> [Parameter] {
    var result: [Parameter] = []
    result.append(pairedWithLoweredType(parameter: program.ast[d].receiver))
    result.append(contentsOf: program.ast[d].parameters.map(pairedWithLoweredType(parameter:)))
    return result
  }

  /// Returns the lowered declarations of `d`'s parameters.
  private func loweredParameters(of d: SubscriptImpl.ID) -> [Parameter] {
    let declType = SubscriptImplType(program[d].type)!
    let captures = declType.captures.lazy.map { (e) in
      program.canonical(e.type, in: program[d].scope)
    }

    var result: [Parameter] = zip(program.captures(of: d), captures).map({ (c, e) in
      if let t = RemoteType(e) {
        return Parameter(decl: c, type: ParameterType(t))
      } else {
        return Parameter(decl: c, type: ParameterType(declType.receiverEffect, e))
      }
    })

    let bundle = SubscriptDecl.ID(program[d].scope)!
    let inputs = program.ast[bundle].parameters
    result.append(contentsOf: inputs.map(pairedWithLoweredType(parameter:)))
    return result
  }

  /// Returns `d`, which declares a parameter, paired with its lowered type.
  private func pairedWithLoweredType(parameter d: ParameterDecl.ID) -> Parameter {
    let t = program.canonical(program[d].type, in: program[d].scope)
    return .init(decl: AnyDeclID(d), type: ParameterType(t)!)
  }

  /// Appends to `inputs` the parameters corresponding to the given `captures` passed `effect`,
  /// canonicalizing theirs type in `scopeOfUse`.
  private func appendCaptures(
    _ captures: [TupleType.Element], passed effect: AccessEffect, to inputs: inout [Parameter],
    canonicalizedIn scopeOfUse: AnyScopeID
  ) {
    inputs.reserveCapacity(captures.count)
    for c in captures {
      switch program.canonical(c.type, in: scopeOfUse).base {
      case let p as RemoteType:
        precondition(p.access != .yielded, "cannot lower yielded parameter")
        inputs.append(.init(decl: nil, type: ParameterType(p)))
      case let p:
        precondition(effect != .yielded, "cannot lower yielded parameter")
        inputs.append(.init(decl: nil, type: ParameterType(effect, ^p)))
      }
    }
  }

  /// Appends `parameters` to `inputs`, canonicalizing their types in `scopeOfUse`.
  private func appendParameters(
    _ parameters: [CallableTypeParameter], to inputs: inout [Parameter],
    canonicalizedIn scopeOfUse: AnyScopeID
  ) {
    inputs.reserveCapacity(parameters.count)
    for p in parameters {
      let t = ParameterType(program.canonical(p.type, in: scopeOfUse))!
      precondition(t.access != .yielded, "cannot lower yielded parameter")
      inputs.append(.init(decl: nil, type: t))
    }
  }

  /// Returns a pointer to the witness table of `t` used in `scopeOfUse`.
  mutating func demandWitnessTable(_ t: AnyType, in scopeOfUse: AnyScopeID) -> WitnessTable {
    let cs = loweredConformances(of: t, exposedTo: scopeOfUse)
    return WitnessTable(for: t, conformingTo: cs, in: scopeOfUse)
  }

  /// Returns the lowered conformances of `model` that are exposed to `useScope`.
  private mutating func loweredConformances(
    of model: AnyType, exposedTo useScope: AnyScopeID
  ) -> Set<IR.Conformance> {
    guard let conformances = program.conformances[model] else { return [] }

    var result: Set<IR.Conformance> = []
    for concept in conformances.keys {
      let c = program.conformance(of: model, to: concept, exposedTo: useScope)!
      result.insert(loweredConformance(c))
    }
    return result
  }

  /// Returns the lowered form of `c`.
  private mutating func loweredConformance(_ c: FrontEnd.Conformance) -> IR.Conformance {
    var implementations = IR.Conformance.ImplementationMap()
    for (r, i) in c.implementations where (r.kind != AssociatedTypeDecl.self) {
      let f = demandDeclaration(lowering: i)
      implementations[r] = .function(FunctionReference(to: f, in: self))
    }
    return .init(concept: c.concept, implementations: implementations)
  }

  /// Returns a map from `f`'s generic arguments to their skolemized form.
  ///
  /// - Requires: `f` is declared in `self`.
  public func specialization(in f: Function.ID) -> GenericArguments {
    var result = GenericArguments()
    for p in functions[f]!.genericParameters {
      guard
        let t = MetatypeType(program[p].type),
        let u = GenericTypeParameterType(t.instance)
      else {
        // TODO: Handle value parameters
        UNIMPLEMENTED()
      }

      result[p] = .type(^u)
    }
    return result
  }

  /// Returns the entry of `f`.
  ///
  /// - Requires: `f` is declared in `self`.
  public func entry(of f: Function.ID) -> Block.ID? {
    functions[f]!.entry.map({ Block.ID(f, $0) })
  }

  /// Returns the operand representing the return value of `f`.
  ///
  /// - Requires: `f` is declared in `self`.
  public func returnValue(of f: Function.ID) -> Operand? {
    let i = functions[f]!
    if !i.isSubscript, let e = entry(of: f) {
      return Operand.parameter(e, i.inputs.count)
    } else {
      return nil
    }
  }

  /// Appends to `f` an entry block that is in `scope`, returning its identifier.
  ///
  /// - Requires: `f` is declared in `self` and doesn't have an entry block.
  @discardableResult
  mutating func appendEntry<T: ScopeID>(in scope: T, to f: Function.ID) -> Block.ID {
    let ir = functions[f]!
    assert(ir.blocks.isEmpty)

    // In functions, the last parameter of the entry denotes the function's return value.
    var parameters = ir.inputs.map({ IR.`Type`.address($0.type.bareType) })
    if !ir.isSubscript {
      parameters.append(.address(ir.output))
    }

    return appendBlock(in: scope, taking: parameters, to: f)
  }

  /// Appends to `f` a basic block that is in `scope` and accepts `parameters` to `f`, returning
  /// its identifier.
  ///
  /// - Requires: `f` is declared in `self`.
  @discardableResult
  mutating func appendBlock<T: ScopeID>(
    in scope: T,
    taking parameters: [IR.`Type`] = [],
    to f: Function.ID
  ) -> Block.ID {
    let a = functions[f]!.appendBlock(in: scope, taking: parameters)
    return Block.ID(f, a)
  }

  /// Removes `block` and updates def-use chains.
  ///
  /// - Requires: No instruction in `block` is used by an instruction outside of `block`.
  @discardableResult
  mutating func removeBlock(_ block: Block.ID) -> Block {
    for i in instructions(in: block) {
      precondition(allUses(of: i).allSatisfy({ $0.user.block == block.address }))
      removeUsesMadeBy(i)
    }
    return functions[block.function]!.removeBlock(block.address)
  }

  /// Swaps `old` by `new`.
  ///
  /// `old` is removed and the def-use chains are updated so that the uses made by `old` are
  /// replaced by the uses made by `new` and all uses of `old` refer to `new`. After the call,
  /// `self[old] == new`.
  ///
  /// - Requires: `new` produces results with the same types as `old`.
  mutating func replace<I: Instruction>(_ old: InstructionID, with new: I) {
    precondition(self[old].result == new.result)
    removeUsesMadeBy(old)
    _ = insert(new) { (m, i) in
      m[old] = i
      return old
    }
  }

  /// Swaps all uses of `old` in `f` by `new` and updates the def-use chains.
  ///
  /// - Requires: `new` as the same type as `old`. `f` is in `self`.
  mutating func replaceUses(of old: Operand, with new: Operand, in f: Function.ID) {
    precondition(old != new)
    precondition(type(of: old) == type(of: new))

    guard var oldUses = uses[old], !oldUses.isEmpty else { return }
    var newUses = uses[new] ?? []

    var end = oldUses.count
    for i in oldUses.indices.reversed() where oldUses[i].user.function == f {
      let u = oldUses[i]
      self[u.user].replaceOperand(at: u.index, with: new)
      newUses.append(u)
      end -= 1
      oldUses.swapAt(i, end)
    }
    oldUses.removeSubrange(end...)

    uses[old] = oldUses
    uses[new] = newUses
  }

  /// Inserts `newInstruction` at `boundary` and returns its identity.
  @discardableResult
  mutating func insert(
    _ newInstruction: Instruction, at boundary: InsertionPoint
  ) -> InstructionID {
    switch boundary {
    case .start(let b):
      return prepend(newInstruction, to: b)
    case .end(let b):
      return append(newInstruction, to: b)
    case .before(let i):
      return insert(newInstruction, before: i)
    case .after(let i):
      return insert(newInstruction, after: i)
    }
  }

  /// Adds `newInstruction` at the start of `block` and returns its identity.
  @discardableResult
  mutating func prepend(_ newInstruction: Instruction, to block: Block.ID) -> InstructionID {
    precondition(!(newInstruction is Terminator), "terminator must appear last in a block")
    return insert(newInstruction) { (m, i) in
      InstructionID(block, m[block].instructions.prepend(newInstruction))
    }
  }

  /// Adds `newInstruction` at the end of `block` and returns its identity.
  @discardableResult
  mutating func append(_ newInstruction: Instruction, to block: Block.ID) -> InstructionID {
    precondition(!(self[block].instructions.last is Terminator), "insertion after terminator")
    return insert(newInstruction) { (m, i) in
      InstructionID(block, m[block].instructions.append(newInstruction))
    }
  }

  /// Inserts `newInstruction` at `position` and returns its identity.
  ///
  /// The instruction is inserted before the instruction currently at `position`. You can pass a
  /// "past the end" position to append at the end of a block.
  @discardableResult
  mutating func insert(
    _ newInstruction: Instruction, at position: InstructionIndex
  ) -> InstructionID {
    precondition(!(newInstruction is Terminator), "terminator must appear last in a block")
    return insert(newInstruction) { (m, i) in
      let address = m.functions[position.function]![position.block].instructions
        .insert(newInstruction, at: position.index)
      return InstructionID(position.function, position.block, address)
    }
  }

  /// Inserts `newInstruction` before `successor` and returns its identity.
  @discardableResult
  mutating func insert(
    _ newInstruction: Instruction, before successor: InstructionID
  ) -> InstructionID {
    precondition(!(newInstruction is Terminator), "terminator must appear last in a block")
    return insert(newInstruction) { (m, i) in
      let address = m.functions[successor.function]![successor.block].instructions
        .insert(newInstruction, before: successor.address)
      return InstructionID(successor.function, successor.block, address)
    }
  }

  /// Inserts `newInstruction` after `predecessor` and returns its identity.
  @discardableResult
  mutating func insert(
    _ newInstruction: Instruction, after predecessor: InstructionID
  ) -> InstructionID {
    precondition(!(instruction(after: predecessor) is Terminator), "insertion after terminator")
    return insert(newInstruction) { (m, i) in
      let address = m.functions[predecessor.function]![predecessor.block].instructions
        .insert(newInstruction, after: predecessor.address)
      return InstructionID(predecessor.function, predecessor.block, address)
    }
  }

  /// Inserts `newInstruction` with `impl` and returns its identity.
  private mutating func insert(
    _ newInstruction: Instruction, with impl: (inout Self, Instruction) -> InstructionID
  ) -> InstructionID {
    // Insert the instruction.
    let user = impl(&self, newInstruction)

    // Update the def-use chains.
    for i in 0..<newInstruction.operands.count {
      uses[newInstruction.operands[i], default: []].append(Use(user: user, index: i))
    }

    return user
  }

  /// Removes instruction `i` and updates def-use chains.
  ///
  /// - Requires: The result of `i` have no users.
  mutating func removeInstruction(_ i: InstructionID) {
    precondition(result(of: i).map(default: true, { uses[$0, default: []].isEmpty }))
    removeUsesMadeBy(i)
    self[i.function][i.block].instructions.remove(at: i.address)
  }

  /// Removes all instructions after `i` in its containing block and updates def-use chains.
  ///
  /// - Requires: Let `S` be the set of removed instructions, all users of a result of `j` in `S`
  ///   are also in `S`.
  mutating func removeAllInstructions(after i: InstructionID) {
    while let a = self[i.function][i.block].instructions.lastAddress, a != i.address {
      removeInstruction(.init(i.function, i.block, a))
    }
  }

  /// Returns the uses of all the registers assigned by `i`.
  func allUses(of i: InstructionID) -> [Use] {
    result(of: i).map(default: [], { uses[$0, default: []] })
  }

  /// Removes `i` from the def-use chains of its operands.
  private mutating func removeUsesMadeBy(_ i: InstructionID) {
    for o in self[i].operands {
      uses[o]?.removeAll(where: { $0.user == i })
    }
  }

  /// Returns the operands from which the address denoted by `a` derives.
  ///
  /// The (static) provenances of an address denote the original operands from which it derives.
  /// They form a set because an address computed by a projection depends on that projection's
  /// arguments and because an address defined as a parameter of a basic block with multiple
  /// predecessors depends on that bock's arguments.
  func provenances(_ a: Operand) -> Set<Operand> {
    // TODO: Block arguments
    guard let i = a.instruction else { return [a] }

    switch self[i] {
    case let s as AdvancedByBytes:
      return provenances(s.base)
    case let s as Access:
      return provenances(s.source)
    case let s as Project:
      return s.operands.reduce(into: []) { (p, o) in
        if type(of: o).isAddress { p.formUnion(provenances(o)) }
      }
    case let s as SubfieldView:
      return provenances(s.recordAddress)
    case let s as WrapExistentialAddr:
      return provenances(s.witness)
    default:
      return [a]
    }
  }

  /// Returns `true` if `o` can be sunken.
  func isSink(_ o: Operand) -> Bool {
    provenances(o).allSatisfy { (p) -> Bool in
      switch p {
      case .parameter(let e, let i):
        if entry(of: e.function) == e {
          return self[e.function].inputs[i].type.access == .sink
        } else {
          return false
        }

      case .register(let i):
        switch self[i] {
        case let s as ProjectBundle:
          return s.capabilities.contains(.sink)
        case let s as Project:
          return s.projection.access == .sink
        default:
          return true
        }

      default:
        return true
      }
    }
  }

  /// Returns `true` iff `o` is an `access [set]` instruction.
  func isBorrowSet(_ o: Operand) -> Bool {
    guard
      let i = o.instruction,
      let s = self[i] as? Access
    else { return false }
    return s.capabilities == [.set]
  }

}
