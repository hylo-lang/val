import Foundation
import Utils

/// A data structure representing a typed Hylo program ready to be lowered.
public struct TypedProgram {

  /// A set of conformances represented to answer "does A conform to T in S" efficiently.
  public typealias ConformanceSet = [AnyType: ConformanceTable]

  /// A table from trait to its conformances for a given type.
  public typealias ConformanceTable = [TraitType: Set<Conformance>]

  /// The program annotated by the properties of `self`.
  private var base: ScopedProgram

  /// A map from translation unit to its imports.
  public internal(set) var imports: [TranslationUnit.ID: Set<ModuleDecl.ID>] = [:]

  /// The overarching type of each declaration.
  public internal(set) var declType: [AnyDeclID: AnyType] = [:]

  /// The type of each expression.
  public internal(set) var exprType: [AnyExprID: AnyType] = [:]

  /// The type of each pattern.
  public internal(set) var patternType: [AnyPatternID: AnyType] = [:]

  /// A map from function and subscript declarations to their implicit captures.
  public internal(set) var implicitCaptures: [AnyDeclID: [ImplicitCapture]] = [:]

  /// A map from generic declarations to their environment.
  public internal(set) var environment: [AnyDeclID: GenericEnvironment] = [:]

  /// A map from module to its synthesized declarations.
  public internal(set) var synthesizedDecls: [ModuleDecl.ID: Set<SynthesizedFunctionDecl>] = [:]

  /// A map from name expression to its referred declaration.
  public internal(set) var referredDecl: BindingMap = [:]

  /// A map from call expression to its operands after desugaring and implicit resolution.
  public internal(set) var callOperands: [CallID: [ArgumentResolutionResult]] = [:]

  /// A map from sequence expressions to their evaluation order.
  public internal(set) var foldedForm: [SequenceExpr.ID: FoldedSequenceExpr] = [:]

  /// A map from functions to their attributes.
  public internal(set) var functionAttributes: [FunctionDecl.ID: FunctionAttributes] = [:]

  /// The conformances in the program.
  public internal(set) var conformances: ConformanceSet = [:]

  /// Creates an instance annotating `base` with semantic information, reporting diagnostics to
  /// `log` and throwing iff an error was found.
  ///
  /// - Parameters:
  ///   - typeCheckingIsParallel: if `true`, the program is partitioned into chucks that are type
  ///     checked separately. Otherwise, type checking is performed sequentially. Either way, the
  ///     order in which declarations are being checked is nondeterministic.
  ///   - shouldTraceInference: A closure accepting a node and its containing program, returning
  ///     `true` if a trace of type inference should be logged on the console for that node. The
  ///     closure is not called if `typeCheckingIsParallel` is `true`.
  public init(
    annotating base: ScopedProgram,
    inParallel typeCheckingIsParallel: Bool = false,
    reportingDiagnosticsTo log: inout DiagnosticSet,
    tracingInferenceIf shouldTraceInference: ((AnyNodeID, TypedProgram) -> Bool)? = nil,
    loggingRequirementSystemIf shouldLogRequirements: ((AnyDeclID, TypedProgram) -> Bool)? = nil,
    profileWith profiler: ProfilingMeasurements? = nil
  ) throws {
    let instanceUnderConstruction = SharedMutable(TypedProgram(partiallyFormedFrom: base))

    if typeCheckingIsParallel {
      let sources = base.ast[base.ast.modules].map(\.sources).joined()
      var tasks: [TypeCheckTask] = []

      for (i, chunk) in sources.chunked(inMax: 255).enumerated() {
        let t = TypeCheckTask(
          Array(chunk), withCheckerIdentifiedBy: UInt8(i),
          collaborativelyConstructing: instanceUnderConstruction,
          tracingInferenceIf: nil,
          loggingRequirementSystemIf: nil)
        tasks.append(t)
      }

      let probe = profiler?.createAndStartProfilingProbe(MeasurementType.TypeChecker)
      defer { probe?.stop() }
      let queue = OperationQueue()
      queue.addOperations(tasks, waitUntilFinished: true)
      for t in tasks {
        log.formUnion(t.diagnostics)
      }
    }

    self = try instanceUnderConstruction.read {
      var checker = TypeChecker(
        constructing: $0,
        tracingInferenceIf: typeCheckingIsParallel ? nil : shouldTraceInference,
        loggingRequirementSystemIf: typeCheckingIsParallel ? nil : shouldLogRequirements)
      let probe = profiler?.createAndStartProfilingProbe(MeasurementType.TypeChecker)
      defer { probe?.stop() }
      checker.checkAllDeclarations()

      log.formUnion(checker.diagnostics)
      try log.throwOnError()
      return checker.program
    }
  }

  /// Returns a copy of `self` in which a new module has been loaded, calling `make` to form its
  /// contents and reporting diagnostics to `log`.
  ///
  /// - Parameters:
  ///   - shouldTraceInference: A closure accepting a node and its containing program, returning
  ///     `true` if a trace of type inference should be logged on the console for that node.
  public func loadModule(
    reportingDiagnosticsTo log: inout DiagnosticSet,
    tracingInferenceIf shouldTraceInference: ((AnyNodeID, TypedProgram) -> Bool)? = nil,
    loggingRequirementSystemIf shouldLogRequirements: ((AnyDeclID, TypedProgram) -> Bool)? = nil,
    creatingContentsWith make: AST.ModuleLoader,
    profileWith profiler: ProfilingMeasurements? = nil
  ) throws -> (Self, ModuleDecl.ID) {
    let (p, m) = try base.loadModule(reportingDiagnosticsTo: &log, creatingContentsWith: make)
    var extended = self
    extended.base = consume p

    var checker = TypeChecker(
      constructing: extended,
      tracingInferenceIf: shouldTraceInference,
      loggingRequirementSystemIf: shouldLogRequirements)

    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.TypeChecker)
    defer { probe?.stop() }
    checker.checkModule(m)

    log.formUnion(checker.diagnostics)
    try log.throwOnError()
    return (checker.program, m)
  }

  /// The type checking of a collection of source files.
  private final class TypeCheckTask: Operation, @unchecked Sendable {

    /// The sources to check.
    private let sources: [TranslationUnit.ID]

    /// The checker used by this operation.
    private var checker: TypeChecker

    /// Creates a task type checking `sources` with a checker identified by `checkerIdentifier`,
    /// constructing `instanceUnderConstruction`.
    init(
      _ sources: [TranslationUnit.ID],
      withCheckerIdentifiedBy checkerIdentifier: UInt8,
      collaborativelyConstructing instanceUnderConstruction: SharedMutable<TypedProgram>,
      tracingInferenceIf shouldTraceInference: ((AnyNodeID, TypedProgram) -> Bool)?,
      loggingRequirementSystemIf shouldLogRequirements: ((AnyDeclID, TypedProgram) -> Bool)?
    ) {
      self.sources = sources
      self.checker = TypeChecker(
        checkerIdentifier,
        collaborativelyConstructing: instanceUnderConstruction,
        tracingInferenceIf: shouldTraceInference,
        loggingRequirementSystemIf: shouldLogRequirements)
    }

    /// Executes the operation.
    override func main() {
      checker.check(sources)
      checker.synchronize()
    }

    /// The diagnostic reported during type checker.
    var diagnostics: DiagnosticSet {
      checker.diagnostics
    }

  }

  /// Creates a partially formed instance with empty property in preparation for type checking.
  private init(partiallyFormedFrom base: ScopedProgram) {
    self.base = base
  }

  /// Returns the canonical form of `d`'s type.
  public func canonical<T: DeclID>(typeOf d: T) -> AnyType {
    canonical(declType[d]!, in: nodeToScope[d]!)
  }

  /// Returns the canonical form of `e`'s type.
  public func canonical<T: ExprID>(typeOf e: T) -> AnyType {
    canonical(exprType[e]!, in: nodeToScope[e]!)
  }

  /// Returns the canonical form of `t` in `scopeOfUse`.
  public func canonical(_ t: AnyType, in scopeOfUse: AnyScopeID) -> AnyType {
    if t.isCanonical { return t }
    var checker = TypeChecker(asContextFor: self)
    return checker.canonical(t, in: scopeOfUse)
  }

  /// Returns the canonical form of `v` in `scopeOfUse`.
  public func canonical(_ v: CompileTimeValue, in scopeOfUse: AnyScopeID) -> CompileTimeValue {
    var checker = TypeChecker(asContextFor: self)
    return checker.canonical(v, in: scopeOfUse)
  }

  /// Returns `arguments` with all types replaced by their canonical form in `scopeOfUse`.
  public func canonical(
    _ arguments: GenericArguments, in scopeOfUse: AnyScopeID
  ) -> GenericArguments {
    var checker = TypeChecker(asContextFor: self)
    return checker.canonical(arguments, in: scopeOfUse)
  }

  /// Returns true iff t and u are semantically equivalent in scopeOfUse.
  public func areEquivalent(_ t: AnyType, _ u: AnyType, in scopeOfUse: AnyScopeID) -> Bool {
    var checker = TypeChecker(asContextFor: self)
    return checker.areEquivalent(t, u, in: scopeOfUse)
  }

  /// Returns `generic` with occurrences of parameters keying `specialization` replaced by their
  /// corresponding value, performing necessary name lookups from `scopeOfUse`.
  ///
  /// This method has no effect if `substitutions` is empty.
  public func specialize(
    _ generic: AnyType, for specialization: GenericArguments, in scopeOfUse: AnyScopeID
  ) -> AnyType {
    var checker = TypeChecker(asContextFor: self)
    return checker.specialize(generic, for: specialization, in: scopeOfUse)
  }

  /// Returns `arguments` applying `specialization` on each value in `scopeOfUse`.
  public func specialize(
    _ arguments: GenericArguments, for specialization: GenericArguments,
    in scopeOfUse: AnyScopeID
  ) -> GenericArguments {
    var checker = TypeChecker(asContextFor: self)
    return arguments.mapValues { (v) in
      if case .type(let t) = v {
        return .type(checker.specialize(t, for: specialization, in: scopeOfUse))
      } else {
        UNIMPLEMENTED()
      }
    }
  }

  /// Returns `true` iff deinitializing an instance of `t` in `scopeOfUse` is a no-op.
  ///
  /// A type is "trivially deinitializable" if deinitializing its instances doesn't have runtime
  /// effects. Built-in types are trivially deinitializable. Types composed only of trivially
  /// deinitializable parts are trivially deinitializable unless there exists a non-synthetic
  /// conformance to `Deinitializable` in scope.
  public func isTriviallyDeinitializable(_ t: AnyType, in scopeOfUse: AnyScopeID) -> Bool {
    isTrivialModel(t, of: ast.core.deinitializable.type, in: scopeOfUse)
  }

  /// Returns `true` iff `t` models `coreConcept` without any user-defined semantics.
  private func isTrivialModel(
    _ t: AnyType, of coreConcept: TraitType, in scopeOfUse: AnyScopeID
  ) -> Bool {
    let model = canonical(t, in: scopeOfUse)

    // Built-ins have no conformances, but they are trivial.
    if let c = conformance(of: model, to: coreConcept, exposedTo: scopeOfUse) {
      return isTrivial(c)
    } else {
      return model.isBuiltinOrRawTuple
    }
  }

  /// Returns `true` iff `c` has no user-defined semantics.
  public func isTrivial(_ c: Conformance) -> Bool {
    // Non-synthetic conformances are not trivial.
    if !c.isSynthetic {
      return false
    }

    // Structural types are trivial if their parts are. Other types are trivial if they have their
    // conformance to `coreConcept` was synthesized.
    switch c.model.base {
    case let u as BufferType:
      return isTrivialModel(u.element, of: c.concept, in: c.scope)
    case let u as TupleType:
      return u.elements.allSatisfy({ isTrivialModel($0.type, of: c.concept, in: c.scope) })
    case let u as UnionType:
      return u.elements.allSatisfy({ isTrivialModel($0, of: c.concept, in: c.scope) })
    case is MetatypeType:
      return true
    case let u as ProductType:
      return storage(of: u).allSatisfy({ isTrivialModel($0.type, of: c.concept, in: c.scope) })
    default:
      return false
    }
  }

  /// If `t` has a record layout, returns the names and types of its stored properties.
  public func storage(of t: AnyType) -> [TupleType.Element] {
    switch t.base {
    case let u as ArrowType:
      return storage(of: u)
    case let u as BoundGenericType:
      return storage(of: u)
    case let u as BufferType:
      return storage(of: u)
    case let u as ProductType:
      return storage(of: u)
    case let u as TupleType:
      return u.elements
    case let u as TypeAliasType:
      return storage(of: u.resolved)
    default:
      assert(!t.hasRecordLayout)
      return []
    }
  }

  /// Returns the names and types of `t`'s stored properties.
  public func storage(of t: ArrowType) -> [TupleType.Element] {
    return [
      TupleType.Element(label: "__f", type: .builtin(.ptr)),
      TupleType.Element(label: "__e", type: t.environment),
    ]
  }

  /// Returns the names and types of `t`'s stored properties.
  public func storage(of t: BoundGenericType) -> [TupleType.Element] {
    storage(of: t.base).map { (p) in
      // FIXME: Probably wrong to specialize/canonicalize in any random scope.
      let arbitraryScope = AnyScopeID(base.ast.coreLibrary!)
      let z = GenericArguments(t)
      let u = specialize(p.type, for: z, in: arbitraryScope)
      let v = canonical(u, in: arbitraryScope)
      return .init(label: p.label, type: v)
    }
  }

  /// Returns the names and types of `t`'s stored properties.
  public func storage(of t: BufferType) -> [TupleType.Element] {
    if let w = ConcreteTerm(t.count)?.value as? Int {
      return Array(repeating: .init(label: nil, type: t.element), count: w)
    } else {
      return []
    }
  }

  /// Returns the names and types of `t`'s stored properties.
  public func storage(of t: ProductType) -> [TupleType.Element] {
    var result: [TupleType.Element] = []
    for b in ast[t.decl].members.filter(BindingDecl.self) {
      for (_, n) in ast.names(in: ast[b].pattern) {
        let partName = ast[ast[n].decl].baseName
        let partType = canonical(declType[ast[n].decl]!, in: AnyScopeID(t.decl))
        result.append(.init(label: partName, type: partType))
      }
    }
    return result
  }

  /// Returns generic parameters captured by `s` and the scopes semantically containing `s`.
  public func accumulatedGenericParameters<T: ScopeID>(
    in s: T
  ) -> [GenericParameterDecl.ID] {
    var checker = TypeChecker(asContextFor: self)
    return checker.accumulatedGenericParameters(in: s)
  }

  /// Returns the trait of which `d` is a member, or `nil` if `d` isn't member of a trait.
  public func traitDeclaring<T: DeclID>(_ d: T) -> TraitType? {
    var checker = TypeChecker(asContextFor: self)
    return checker.traitDeclaring(d)
  }

  /// If `d` is member of a trait `c`, returns `(d, c)` if `d` is a requirement, or `(r, c)` if `d`
  /// is a default implementation of a requirement `r`; returns `nil` otherwise.
  public func requirementDeclaring(_ d: AnyDeclID) -> (decl: AnyDeclID, trait: TraitType)? {
    guard let c = traitDeclaring(d) else { return nil }

    // `d` might be the default definition of itself.
    if isRequirement(d) { return (d, c) }

    // `d` might be the default implementation of some requirement with the same type.
    let s = nodeToScope[d]!
    let n = name(of: d)
    let t = canonical(declType[d]!, in: s)
    let r = ast.requirements(of: c.decl).first { (m) in
      n == name(of: m) && areEquivalent(t, declType[m]!, in: s)
    }
    return r.map({ ($0, c) })
  }

  /// Returns `true` iff `model` conforms to `concept` in `scopeOfUse`.
  public func conforms(
    _ model: AnyType, to concept: TraitType, in scopeOfUse: AnyScopeID
  ) -> Bool {
    conformance(of: model, to: concept, exposedTo: scopeOfUse) != nil
  }

  /// Returns `true` iff all elements in `models` conform to `concept` in `scopeOfUse`.
  public func allConform<S: Sequence<AnyType>>(
    _ models: S, to concept: TraitType, in scopeOfUse: AnyScopeID
  ) -> Bool {
    models.allSatisfy({ conforms($0, to: concept, in: scopeOfUse) })
  }

  /// Returns the conformance of `model` to `concept` that is exposed to `scopeOfUse`, or `nil` if
  /// such a conformance doesn't exist.
  public func conformance(
    of model: AnyType, to concept: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    let m = canonical(model, in: scopeOfUse)

    if let c = concreteConformance(of: m, to: concept, exposedTo: scopeOfUse) { return c }
    if let c = abstractConformance(of: m, to: concept, exposedTo: scopeOfUse) { return c }
    return structuralConformance(of: m, to: concept, exposedTo: scopeOfUse)
  }

  /// Returns the explicitly declared conformance of `model` to `concept` that is exposed to
  /// `scopeOfUse`, or `nil` if such a conformance doesn't exist.
  ///
  /// This method returns `nil` if the conformance of `model` to `concept` is structural (e.g., a
  /// tuple's synthesized conformance to `Movable`) or if the conformance is implied by a trait
  /// bound (e.g., `T: P` in `fun f<T: P>() {}`).
  ///
  /// Do not call `concreteConformance` during type checking.
  ///
  /// - Requires: `model` is canonical.
  private func concreteConformance(
    of model: AnyType, to concept: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    let checker = TypeChecker(asContextFor: self)
    return checker.cachedConformance(of: model, to: concept, exposedTo: scopeOfUse)
  }

  /// Returns the conformance of `model` to `concept` that is implied by the generic environment
  /// introducing `model` in `scopeOfUse`, or `nil` if such a conformance doesn't exist.
  ///
  /// The result of this method is valid iff a call to `concreteConformance(of:to:exposedTo:)` with
  /// the same arguments has returned `nil`.
  ///
  /// - Requires: `model` is canonical.
  private func abstractConformance(
    of model: AnyType, to concept: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    // No implied conformance unless `model` is a generic parameter or associated type.
    if !model.isSkolem { return nil }

    var checker = TypeChecker(asContextFor: self)
    if !checker.conforms(model, to: concept, in: scopeOfUse) { return nil }

    // An abstract conformance maps each requirement to itself.
    var implementations = Conformance.ImplementationMap()
    for requirement in ast.requirements(of: concept.decl) {
      implementations[requirement] = .explicit(requirement)
    }

    return .init(
      model: model, concept: concept, arguments: .empty, conditions: [], scope: scopeOfUse,
      implementations: implementations, isStructural: false, origin: nil)
  }

  /// Returns the implicit structural conformance of `model` to `concept` that is exposed to
  /// `scopeOfUse`, or `nil` if such a conformance doesn't exist.
  private func structuralConformance(
    of model: AnyType, to concept: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    assert(model.isCanonical)

    switch model.base {
    case let m as BufferType:
      // FIXME: To remove once conditional conformance is implemented
      guard conforms(m.element, to: concept, in: scopeOfUse) else { return nil }
    case let m as ArrowType:
      guard conforms(m.environment, to: concept, in: scopeOfUse) else { return nil }
    case let m as TupleType:
      guard allConform(m.elements.map(\.type), to: concept, in: scopeOfUse) else { return nil }
    case let m as UnionType:
      guard allConform(m.elements, to: concept, in: scopeOfUse) else { return nil }
    case is MetatypeType:
      break
    case is RemoteType where concept == ast.core.deinitializable.type:
      break
    default:
      return nil
    }

    // We could predict that codegen won't need some of the skolems we gather here to reduce the
    // number of generic functions that we define.
    let g = accumulatedGenericParameters(in: scopeOfUse)
    let h = g.filter(model.skolems.contains(_:))

    var implementations = Conformance.ImplementationMap()
    for requirement in ast.requirements(of: concept.decl) {
      guard let k = ast.synthesizedKind(of: requirement) else { return nil }

      var a = GenericArguments.empty
      a[ast[concept.decl].receiver] = .type(model)

      let t = ArrowType(specialize(declType[requirement]!, for: a, in: scopeOfUse))!
      let d = SynthesizedFunctionDecl(k, typed: t, parameterizedBy: h, in: scopeOfUse)
      implementations[requirement] = .synthetic(d)
    }

    let z = GenericArguments(skolemizing: h, in: ast)
    return .init(
      model: model, concept: concept, arguments: z, conditions: [], scope: scopeOfUse,
      implementations: implementations, isStructural: true, origin: nil)
  }

  /// Returns the type satisfying the associated type requirement `n` in conformance `c`.
  ///
  /// - Requires: `n` is declared by the trait for which `c` has been established.
  public func associatedType(_ n: AssociatedTypeDecl.ID, for c: Conformance) -> AnyType {
    let d = c.implementations[n]!.decl!
    let s: AnyScopeID = c.origin.flatMap({ (o) in AnyScopeID(o.source) }) ?? c.scope
    let t = specialize(MetatypeType(declType[d]!)!.instance, for: c.arguments, in: s)
    return canonical(t, in: c.scope)
  }

  /// Returns the foreign representation of `t` using its conformance to `ForeignConvertible` in
  /// `scopeOfUse`.
  ///
  /// - Requires: `t` conforms to `ForeignConvertible` in `scopeOfUse`.
  public func foreignRepresentation(
    of t: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> AnyType {
    let f = ast.core.foreignConvertible
    let d = f.foreignRepresentation

    // Since conformances of built-in types are not stored in property maps, we'll exit the loop
    // when we assign one to `result`.
    var result = t
    while let c = conformance(of: result, to: f.type, exposedTo: scopeOfUse) {
      // `d` is an associated type declaration so its implementations must have a metatype.
      let i = c.implementations[d]!.decl!
      result = MetatypeType(canonical(self[i].type, in: self[d].scope))!.instance
    }

    return result
  }

  /// Returns the modules visible to `s`.
  public func modules(exposedTo s: AnyScopeID) -> Set<ModuleDecl.ID> {
    if let m = ModuleDecl.ID(s) {
      return [m]
    } else {
      return imports[source(containing: s), default: []]
    }
  }

  /// Returns the type of `d` specialized by `specialization` in `scopeOfUse`.
  public func canonicalType<T: Decl>(
    of d: T.ID, specializedBy specialization: GenericArguments, in scopeOfUse: AnyScopeID
  ) -> AnyType {
    let t = specialize(self[d].type, for: specialization, in: scopeOfUse)
    return canonical(t, in: scopeOfUse)
  }

  /// Returns the declarations of `d`'s captures.
  ///
  /// If `d` is a member, its receiver is its only capture. Otherwise, this method returns
  /// `nonMemberCaptures(d)`.
  public func captures(of d: FunctionDecl.ID) -> [AnyDeclID] {
    if let r = ast[d].receiver {
      return [AnyDeclID(r)]
    }
    return nonMemberCaptures(of: d)
  }

  /// Returns the declarations of `d`'s captures.
  ///
  /// If `d` is a member, its receiver is its only capture. Otherwise, this method returns
  /// `nonMemberCaptures(d)`.
  public func captures(of d: SubscriptImpl.ID) -> [AnyDeclID] {
    if let r = ast[d].receiver {
      return [AnyDeclID(r)]
    }
    return nonMemberCaptures(of: SubscriptDecl.ID(nodeToScope[d]!)!)
  }

  /// Returns the declarations of `d`'s captures.
  ///
  /// Explicit captures come first, in the order they appear in its capture list, from left to
  /// right. Implicit captures come next, in the order they were found during type checking.
  ///
  /// - Requires: `d` is not a member declaration.
  public func nonMemberCaptures<T: CapturingDecl>(of d: T.ID) -> [AnyDeclID] {
    var result: [AnyDeclID] = []
    for e in ast[d].explicitCaptures {
      for (_, n) in ast.names(in: ast[e].pattern) {
        result.append(AnyDeclID(ast[n].decl))
      }
    }
    for n in implicitCaptures[d]! {
      result.append(AnyDeclID(n.decl))
    }
    return result
  }

  /// Returns the run-time parameters of `e`, which is the callee of a function or subscript call,
  /// if `e` is a reference to a callable declaration.
  public func runtimeParameters(of callee: AnyExprID) -> [ParameterDecl.ID]? {
    switch callee.kind {
    case InoutExpr.self:
      return runtimeParameters(of: ast[InoutExpr.ID(callee)!].subject)
    case NameExpr.self:
      return referredDecl[NameExpr.ID(callee)!]?.decl.flatMap(ast.runtimeParameters(of:))
    default:
      return nil
    }
  }

  /// Applies `merge(self[keyPath: path], value)`.
  ///
  /// - Parameter merge: A closure that merges `value` into the value currently stored at `path`,
  ///   guaranteeing that the result of the merge is a refinement.
  mutating func write<V>(
    _ value: V, at path: WritableKeyPath<Self, V>,
    mergingWith merge: (inout V, V) -> Void
  ) {
    modify(&self[keyPath: path], { (u) in merge(&u, value) })
  }

  /// Writes `value` at `path`.
  ///
  /// - Requires: `value` contains at least as much information as `self[keyPath: path]`.
  mutating func write<V>(
    _ value: V, at path: WritableKeyPath<Self, V>
  ) where V: Monotonic {
    write(value, at: path) { (u, v) in u.updateMonotonically(v) }
  }

}

extension TypedProgram: Program {

  /// The AST of the program.
  public var ast: AST { base.ast }

  /// A map from node to the innermost scope that contains it.
  public var nodeToScope: ASTProperty<AnyScopeID> { base.nodeToScope }

  /// A map from scope to the declarations directly contained in it.
  public var scopeToDecls: ASTProperty<DeclIDs> { base.scopeToDecls }

  /// A map from variable declaration its containing binding declaration.
  public var varToBinding: [VarDecl.ID: BindingDecl.ID] { base.varToBinding }

}
