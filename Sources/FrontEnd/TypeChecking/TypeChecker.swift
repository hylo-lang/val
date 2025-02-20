import OrderedCollections
import Utils

/// The transformation from a `ScopedProgram` to a `TypedProgram`.
///
/// - Note: A method named with a leading underscore are meant be called only by the method with
///   the same name but without that leading underscore. The former typically implement the actual
///   computation of a value that is memoized by the latter.
struct TypeChecker {

  /// The diagnostics of the type errors.
  private(set) var diagnostics = DiagnosticSet()

  /// An identifier for this instance, unique across concurrent type checking tasks.
  private let identifier: UInt8

  /// The identifier of the next fresh variable.
  private var nextFreshVariableIdentifier: UInt64 = 0

  /// The representation under construction.
  private var cache: Cache

  /// A closure that accepts a node with its containing program and returns `true` if a trace of
  /// type inference should be logged on the console for that node.
  private let shouldTraceInference: ((AnyNodeID, TypedProgram) -> Bool)?

  /// A closure that accepts a generic declaration with its containing program and returns `true`
  /// if the requirement system of its environment should be logged on the console.
  private let shouldLogRequirementSystem: ((AnyDeclID, TypedProgram) -> Bool)?

  /// The local copy of the program being type checked.
  var program: TypedProgram {
    cache.local
  }

  /// Creates an instance as context for algorithms on `p`, whose property are already complete.
  init(asContextFor p: TypedProgram) {
    self.identifier = 0
    self.cache = Cache(local: p)
    self.shouldTraceInference = nil
    self.shouldLogRequirementSystem = nil
  }

  /// Creates an instance for constructing `instanceUnderConstruction`.
  init(
    constructing instanceUnderConstruction: TypedProgram,
    tracingInferenceIf shouldTraceInference: ((AnyNodeID, TypedProgram) -> Bool)?,
    loggingRequirementSystemIf shouldLogRequirements: ((AnyDeclID, TypedProgram) -> Bool)?
  ) {
    self.identifier = 0
    self.cache = Cache(local: instanceUnderConstruction)
    self.shouldTraceInference = shouldTraceInference
    self.shouldLogRequirementSystem = shouldLogRequirements
  }

  /// Creates an instance with given `identifier` for constructing `instanceUnderConstruction`
  /// collaboratively with other instances.
  ///
  /// - Requires: `identifier` is unique across collaborating instances.
  init(
    _ identifier: UInt8,
    collaborativelyConstructing instanceUnderConstruction: SharedMutable<TypedProgram>,
    tracingInferenceIf shouldTraceInference: ((AnyNodeID, TypedProgram) -> Bool)?,
    loggingRequirementSystemIf shouldLogRequirements: ((AnyDeclID, TypedProgram) -> Bool)?
  ) {
    self.identifier = identifier
    self.nextFreshVariableIdentifier = UInt64(identifier) << 56
    self.cache = instanceUnderConstruction.read(
      applying: { Cache(local: $0, shared: instanceUnderConstruction) })
    self.shouldTraceInference = shouldTraceInference
    self.shouldLogRequirementSystem = shouldLogRequirements
  }

  /// Reports the given diagnostic.
  private mutating func report(_ d: Diagnostic) {
    diagnostics.insert(d)
  }

  /// Reports the given diagnostics.
  private mutating func report<S: Sequence<Diagnostic>>(_ batch: S) {
    diagnostics.formUnion(batch)
  }

  // MARK: Type relations

  /// Returns the canonical form of `t` in `scopeOfUse`.
  mutating func canonical(_ t: AnyType, in scopeOfUse: AnyScopeID) -> AnyType {
    if t.isCanonical { return t }

    let r: AnyType
    switch t.base {
    case let u as AssociatedTypeType:
      r = canonical(u, in: scopeOfUse)
    case let u as BoundGenericType:
      r = canonical(u, in: scopeOfUse)
    case let u as TypeAliasType:
      r = canonical(u.aliasee.value, in: scopeOfUse)
    case let u as UnionType:
      r = canonical(u, in: scopeOfUse)
    default:
      r = t.transformParts(mutating: &self, { .stepOver($0.canonical($1, in: scopeOfUse)) })
    }

    assert(r.isCanonical)
    return r
  }

  /// Returns the canonical form of `t` in `scopeOfUse`.
  private mutating func canonical(_ t: AssociatedTypeType, in scopeOfUse: AnyScopeID) -> AnyType {
    if let u = demandImplementation(of: t.decl, for: t.domain, in: scopeOfUse) {
      return canonical(u, in: scopeOfUse)
    } else {
      return .error
    }
  }

  /// Returns the canonical form of `t` in `scopeOfUse`.
  private mutating func canonical(_ t: BoundGenericType, in scopeOfUse: AnyScopeID) -> AnyType {
    if t.isCanonical { return ^t }

    let b = canonical(t.base, in: scopeOfUse)
    let a = canonical(GenericArguments(t), in: scopeOfUse)
    let s = specialize(b, for: a, in: scopeOfUse)
    return canonical(s, in: scopeOfUse)
  }

  /// Returns the canonical form of `t` in `scopeOfUse`.
  private mutating func canonical(_ t: UnionType, in scopeOfUse: AnyScopeID) -> AnyType {
    if t.isCanonical { return ^t }

    var elements = Set<AnyType>()
    for e in t.elements {
      elements.insert(canonical(e, in: scopeOfUse))
    }
    return elements.uniqueElement ?? ^UnionType(elements)
  }

  /// Returns the canonical form of `v` in `scopeOfUse`.
  mutating func canonical(
    _ v: CompileTimeValue, in scopeOfUse: AnyScopeID
  ) -> CompileTimeValue {
    if case .type(let t) = v {
      return .type(canonical(t, in: scopeOfUse))
    } else {
      return v
    }
  }

  /// Returns `arguments` with all types replaced by their canonical form in `scopeOfUse`.
  mutating func canonical(
    _ arguments: GenericArguments, in scopeOfUse: AnyScopeID
  ) -> GenericArguments {
    arguments.mapValues({ canonical($0, in: scopeOfUse) })
  }

  /// Returns `true` iff `t` and `u` are semantically equivalent in `scopeOfUse`.
  mutating func areEquivalent(_ t: AnyType, _ u: AnyType, in scopeOfUse: AnyScopeID) -> Bool {
    let lhs = canonical(t, in: scopeOfUse)
    let rhs = canonical(u, in: scopeOfUse)

    if lhs == rhs {
      return true
    } else if let s = program.scopes(from: scopeOfUse).first(where: \.isGenericScope) {
      return environment(of: s)!.areEquivalent(lhs, rhs, querying: &self)
    } else {
      return false
    }
  }

  /// Returns `true` iff `t` is a refinement of `u` and `t != u`.
  mutating func isStrictRefinement(_ t: TraitType, of u: TraitType) -> Bool {
    (t != u) && bases(of: t).contains(u)
  }

  /// Returns the traits which `t` refines, reporting a cycle if one of them is in `bases`.
  ///
  /// `knownBases` serves as a memo to catch refinement cycles and is expected to be empty except
  /// in recursive calls to `bases(of:knownBases:)`.
  private mutating func bases(
    of t: TraitType, knownToRefine knownBases: Set<TraitType> = []
  ) -> RefinementClosure {
    if let r = cache.traitToBases[t] { return r }

    let newKnownBases = knownBases.inserting(t)
    var result = RefinementClosure(t)

    for (n, s) in evalTraitComposition(program[t.decl].bounds) {
      if newKnownBases.contains(s) {
        report(.error(circularRefinementAt: program[n].site))
      } else {
        let newBases = bases(of: s, knownToRefine: newKnownBases)
        result.insert(newBases, inheritedBy: t)
      }
    }

    cache.traitToBases[t] = result
    return result
  }

  /// Returns the traits to which `t` is declared conforming in `scopeOfUse`.
  mutating func conformedTraits(
    of t: AnyType, in scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    // Computation is not memoized for generic type parameters because queries might come from
    // generic arguments under construction.
    if let u = GenericTypeParameterType(t) {
      return conformedTraits(of: u, in: scopeOfUse)
    }

    let key = Cache.TypeLookupKey(t, in: scopeOfUse)
    if let r = cache.typeToConformedTraits[key] {
      return r
    }

    var result: Set<TraitType>
    switch t.base {
    case let u as AssociatedTypeType:
      result = conformedTraits(of: u, in: scopeOfUse)
    case let u as BoundGenericType:
      result = conformedTraits(of: u.base, in: scopeOfUse)
    case let u as BuiltinType:
      result = conformedTraits(of: u, in: scopeOfUse)
    case let u as ProductType:
      result = conformedTraits(of: u, in: scopeOfUse)
    case let u as TraitType:
      result = bases(of: u).unordered
    case let u as TypeAliasType:
      result = conformedTraits(of: u.resolved, in: scopeOfUse)
    case let u as WitnessType:
      result = conformedTraits(of: u, in: scopeOfUse)
    default:
      result = conformedTraits(declaredInExtensionsOf: t, exposedTo: scopeOfUse)
    }

    cache.typeToConformedTraits[key] = result
    return result
  }

  /// Returns the traits to which `t` is declared conforming in `scopeOfUse`.
  private mutating func conformedTraits(
    of t: AssociatedTypeType, in scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    var result = Set<TraitType>()
    accumulateConformedTraits(declaredInTraitsRequiring: t, suffixedBy: [], in: &result)
    result.formUnion(conformedTraits(declaredByConstraintsOn: ^t, exposedTo: scopeOfUse))
    result.formUnion(conformedTraits(declaredInExtensionsOf: ^t, exposedTo: scopeOfUse))
    return result
  }

  /// Gathers the traits to which the associated type identified by `base` and `suffix` conform.
  ///
  /// The traits to which an associated type conforms can be declared in the trait introducing it
  /// as well as any of the trait defining its qualification. For example, given a type `T.X.Y`, a
  /// a conformance `X.Y: P` could be declared in the trait introducing `X`. Hence, to collect all
  /// possible traits, one must gather the conformances of `Y` in the trait defining `Y` **and**
  /// the conformances of `X.Y` in the traits defining `X`.
  ///
  /// `base` is the qualification of the associated type composed of `suffix` in reverse order. For
  /// example, the base `T.X` and suffix `[Z, Y]` denote the associated type `T.X.Y.Z`.
  private mutating func accumulateConformedTraits(
    declaredInTraitsRequiring base: AssociatedTypeType,
    suffixedBy suffix: [AssociatedTypeDecl.ID],
    in accumulator: inout Set<TraitType>
  ) {
    // Gather the conformances declared in the trait definition `t`.
    var definition = MetatypeType(uncheckedType(of: base.decl))!.instance
    for a in suffix.reversed() {
      definition = ^AssociatedTypeType(a, domain: definition, ast: program.ast)
    }

    let d = TraitDecl.ID(program[base.decl].scope)!
    let e = possiblyPartiallyFormedEnvironment(of: AnyDeclID(d))!
    accumulator.formUnion(e.conformedTraits(of: ^base, querying: &self))

    // Gather the conformances declared as associated type constraints in the traits defining the
    // domain of `t`.
    switch base.domain.base {
    case is GenericTypeParameterType:
      break

    case let u as AssociatedTypeType:
      accumulateConformedTraits(
        declaredInTraitsRequiring: u, suffixedBy: suffix + [base.decl], in: &accumulator)

    case is ConformanceLensType:
      UNIMPLEMENTED("name lookup into conformance lenses")

    default:
      unreachable("unexpected associated type domain '\(base.domain)'")
    }
  }

  /// Returns the traits to which `t` is declared conforming in `scopeOfUse`.
  private func conformedTraits(
    of t: BuiltinType, in scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    if t == .module { return [] }

    return [
      program.ast.core.movable.type,
      program.ast.core.deinitializable.type,
      program.ast.core.foreignConvertible.type,
    ]
  }

  /// Returns the traits to which `t` is declared conforming in `scopeOfUse`.
  private mutating func conformedTraits(
    of t: GenericTypeParameterType, in scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    let scopeOfDeclaration = program[t.decl].scope

    // Trait receivers conform to their traits.
    var result: Set<TraitType>
    if let d = TraitDecl.ID(scopeOfDeclaration) {
      result = bases(of: TraitType(d, ast: program.ast)).unordered
    } else if !isNotionallyContained(scopeOfUse, in: scopeOfDeclaration) {
      let e = possiblyPartiallyFormedEnvironment(of: AnyDeclID(scopeOfDeclaration)!)!
      result = Set(e.conformedTraits(of: ^t, querying: &self))
    } else {
      result = []
    }

    result.formUnion(conformedTraits(declaredByConstraintsOn: ^t, exposedTo: scopeOfUse))
    result.formUnion(conformedTraits(declaredInExtensionsOf: ^t, exposedTo: scopeOfUse))
    return result
  }

  /// Returns the traits to which `t` is declared conforming in `scopeOfUse`.
  private mutating func conformedTraits(
    of t: ProductType, in scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    var result = Set<TraitType>()
    for (_, u) in evalTraitComposition(program[t.decl].conformances) {
      result.formUnion(bases(of: u).unordered)
    }

    result.formUnion(conformedTraits(declaredInExtensionsOf: ^t, exposedTo: scopeOfUse))
    return result
  }

  /// Returns the traits to which `t` can be assumed to be conforming in `scopeOfUse`.
  private mutating func conformedTraits(
    of t: WitnessType, in scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    switch t.container.interface {
    case .traits(let traits):
      return traits.reduce(into: []) { (result, u) in
        result.formUnion(bases(of: u).unordered)
      }

    default:
      UNIMPLEMENTED()
    }
  }

  /// Returns the traits to which `t` is declared conforming by conformance declarations exposed
  /// to `scopeOfUse`.
  private mutating func conformedTraits(
    declaredInExtensionsOf t: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    var result = Set<TraitType>()
    for e in extensions(of: t, exposedTo: scopeOfUse).filter(ConformanceDecl.self) {
      for (_, u) in evalTraitComposition(program[e].conformances) {
        result.formUnion(bases(of: u).unordered)
      }
    }
    return result
  }

  /// Returns the traits to which `t` is declared conforming in its generic environment.
  ///
  /// `t` is a generic type parameter or an associated type introduced by a generic environment
  /// notionally containing `scopeOfUse`. The return value is the set of traits used as bounds of
  /// `t` in that environment.
  private mutating func conformedTraits(
    declaredByConstraintsOn t: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<TraitType> {
    if let s = program.scopes(from: scopeOfUse).first(where: \.isGenericScope) {
      let e = possiblyPartiallyFormedEnvironment(of: AnyDeclID(s)!)!
      return Set(e.conformedTraits(of: ^t, querying: &self))
    } else {
      return []
    }
  }

  /// Returns `true` if `m` conforms to `c` explicitly or structurally in `scopeOfUse`.
  ///
  /// See also `explicitlyConforms` and `structurallyConforms`.
  mutating func conforms(
    _ m: AnyType, to c: TraitType, in scopeOfUse: AnyScopeID
  ) -> Bool {
    explicitlyConforms(m, to: c, in: scopeOfUse) || structurallyConforms(m, to: c, in: scopeOfUse)
  }

  /// Returns `true` if `model` conforms to `trait` explicitly in `scopeOfUse`.
  ///
  /// A conformance is explicit if it has been declared in sources, or if it is the consequence of
  /// generic requirements written in sources.
  private mutating func explicitlyConforms(
    _ model: AnyType, to trait: TraitType, in scopeOfUse: AnyScopeID
  ) -> Bool {
    conformedTraits(of: model, in: scopeOfUse).contains(trait)
  }

  /// Returns `true` if `model` structurally conforms to `trait` in `scopeOfUse`.
  ///
  /// Given a trait describing basis operations (e.g., copy) of values, a structural conformance
  /// *M: T* holds iff all the stored parts of *M* conform to *T*, structurally or otherwise. In
  /// that case, the conformance can be synthesized because its implementation is obvious.
  private mutating func structurallyConforms(
    _ model: AnyType, to trait: TraitType, in scopeOfUse: AnyScopeID
  ) -> Bool {
    switch model.base {
    case is BoundGenericType:
      let m = canonical(model, in: scopeOfUse)
      return !(m.base is BoundGenericType) && structurallyConforms(m, to: trait, in: scopeOfUse)
    case let m as BufferType:
      // FIXME: To remove once conditional conformance is implemented
      return conforms(m.element, to: trait, in: scopeOfUse)
    case let m as ArrowType:
      return conforms(m.environment, to: trait, in: scopeOfUse)
    case is MetatypeType:
      return true
    case let m as RemoteType:
      return conforms(m.bareType, to: trait, in: scopeOfUse)
    case let m as TupleType:
      return m.elements.allSatisfy({ conforms($0.type, to: trait, in: scopeOfUse) })
    case let m as TypeAliasType:
      return structurallyConforms(m.aliasee.value, to: trait, in: scopeOfUse)
    case let m as UnionType:
      return m.elements.allSatisfy({ conforms($0, to: trait, in: scopeOfUse) })
    default:
      return false
    }
  }

  /// Returns `true` if implementations of `trait`'s requirements can be synthesized for `model` in
  /// `scopeOfImplementation`.
  ///
  /// A conformance *M: T* is synthesizable iff *M* structurally conforms to *T*.
  private mutating func canSynthesizeConformance(
    _ model: AnyType, to trait: TraitType, in scopeOfImplementation: AnyScopeID
  ) -> Bool {
    switch model.base {
    case let m as BoundGenericType:
      return canSynthesizeConformance(m, to: trait, in: scopeOfImplementation)
    case let m as ProductType:
      return canSynthesizeConformance(m, to: trait, in: scopeOfImplementation)
    default:
      return structurallyConforms(model, to: trait, in: scopeOfImplementation)
    }
  }

  /// Returns `true` if implementations of `trait`'s requirements can be synthesized for `model` in
  /// `scopeOfImplementation`.
  private mutating func canSynthesizeConformance(
    _ model: BoundGenericType, to trait: TraitType, in scopeOfImplementation: AnyScopeID
  ) -> Bool {
    let base = canonical(model.base, in: scopeOfImplementation)
    let z = GenericArguments(model)

    // If the base is a product type, we specialize each stored part individually to check whether
    // the conformance holds for a specialized whole. Othwrwise, we specialize the base directly.
    if let b = ProductType(base) {
      return program.storedParts(of: b.decl).allSatisfy { (p) in
        let t = specialize(uncheckedType(of: p), for: z, in: scopeOfImplementation)
        return conforms(t, to: trait, in: scopeOfImplementation)
      }
    } else {
      let t = specialize(base, for: z, in: scopeOfImplementation)
      return canSynthesizeConformance(t, to: trait, in: scopeOfImplementation)
    }
  }

  /// Returns `true` if implementations of `trait`'s requirements can be synthesized for `model` in
  /// `scopeOfImplementation`.
  private mutating func canSynthesizeConformance(
    _ model: ProductType, to trait: TraitType, in scopeOfImplementation: AnyScopeID
  ) -> Bool {
    program.storedParts(of: model.decl).allSatisfy { (p) in
      conforms(uncheckedType(of: p), to: trait, in: scopeOfImplementation)
    }
  }

  /// Returns the checked conformance of `model` to `trait` that is exposed to `scopeOfUse`, or
  /// `nil` if such a conformance doesn't exist.
  private mutating func demandConformance(
    of model: AnyType, to trait: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    // As results already in cache may be shadowed by a conformance that hasn't been checked yet,
    // we have to check all conformance sources in scope before we can be sure we'll grab the right
    // one when we call `cachedConformance`.
    let m = canonical(model, in: scopeOfUse)
    let r = bases(of: trait)
    let s = originsOfConformance(of: m, to: trait, exposedTo: scopeOfUse)
    for o in s {
      checkConformances(to: r, declaredBy: o.source)
    }

    // If the conformance is still not in cache, `model` does not conform to `trait`.
    return cachedConformance(of: m, to: trait, exposedTo: scopeOfUse)
  }

  /// Returns the checked conformance of `model` to `trait` that is exposed to `scopeOfUse`, or
  /// `nil` if such a conformance doesn't exist or hasn't been checked yet.
  ///
  /// The result is the innermost available conformance of `model` to `trait` in `scopeOfUse` iff
  /// all possible sources have already been checked. Otherwise, the returned conformance may be
  /// shadowed by one that hasn't been checked yet.
  ///
  /// - Requires: `model` is canonical.
  func cachedConformance(
    of model: AnyType, to trait: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    assert(model.isCanonical)

    // `A<X>: T` iff `A: T`.
    if let t = BoundGenericType(model) {
      return cachedConformance(of: t, to: trait, exposedTo: scopeOfUse)
    }

    guard
      let allConformances = cache.local.conformances[model],
      let conformancesToTrait = allConformances[trait]
    else { return nil }
    return closestConformance(in: conformancesToTrait, exposedTo: scopeOfUse)
  }

  /// Returns the checked conformance of `model` to `trait` that is exposed to `scopeOfUse`, or
  /// `nil` if such a conformance doesn't exist or hasn't been checked yet.
  ///
  /// The result is the innermost available conformance of `model` to `trait` in `scopeOfUse` iff
  /// all possible sources have already been checked. Otherwise, the returned conformance may be
  /// shadowed by one that hasn't been checked yet.
  ///
  /// - Requires: `model` is canonical.
  private func cachedConformance(
    of model: BoundGenericType, to trait: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    guard let c = cachedConformance(of: model.base, to: trait, exposedTo: scopeOfUse) else {
      return nil
    }

    return .init(
      model: model.base, concept: trait, arguments: GenericArguments(model), conditions: [],
      scope: c.scope, implementations: c.implementations, isStructural: c.isStructural,
      origin: c.origin)
  }

  /// Returns the innermost element in `conformances` that is exposed to `scopeOfUse`.
  private func closestConformance<C: Collection<Conformance>>(
    in conformances: C, exposedTo scopeOfUse: AnyScopeID
  ) -> Conformance? {
    let exposed = program.modules(exposedTo: scopeOfUse)
    return
      conformances
      .filter { (c) in
        if let m = ModuleDecl.ID(c.scope), exposed.contains(m) {
          return true
        } else {
          return program.isContained(scopeOfUse, in: c.scope)
        }
      }
      .minimalElements { (a, b) in
        program.compareLexicalDepth(a.scope, b.scope, in: scopeOfUse)
      }
      .uniqueElement
  }

  /// Returns the origins of the conformances of `model` to `trait` exposed to `scopeOfUse`.
  private mutating func originsOfConformance(
    of model: AnyType, to trait: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> [ConformanceOrigin] {
    switch model.base {
    case let t as BoundGenericType:
      return originsOfConformance(of: t.base, to: trait, exposedTo: scopeOfUse)
    case let t as ProductType:
      return originsOfConformance(of: t, to: trait, exposedTo: scopeOfUse)
    case let t as TypeAliasType:
      return originsOfConformance(of: t.resolved, to: trait, exposedTo: scopeOfUse)
    default:
      return originsOfConformance(to: trait, declaredInExtensionsOf: model, exposedTo: scopeOfUse)
    }
  }

  /// Returns the origins of the conformances of `model` to `trait` exposed to `scopeOfUse`.
  private mutating func originsOfConformance(
    of model: ProductType, to trait: TraitType, exposedTo scopeOfUse: AnyScopeID
  ) -> [ConformanceOrigin] {
    let d = ProductTypeDecl.ID(model.decl)!
    let r = originsOfConformance(to: trait, declaredBy: d, exposedTo: scopeOfUse)
    let s = originsOfConformance(to: trait, declaredInExtensionsOf: ^model, exposedTo: scopeOfUse)
    return r + s
  }

  /// Returns the origins of conformances to `trait` exposed to `scopeOfUse` and declared `d`.
  private mutating func originsOfConformance<T: ConformanceSource>(
    to trait: TraitType, declaredBy d: T.ID, exposedTo scopeOfUse: AnyScopeID
  ) -> [ConformanceOrigin] {
    var result: [ConformanceOrigin] = []
    let s = evalTraitComposition(program[d].conformances)
    for (n, t) in s {
      if explicitlyConforms(^t, to: trait, in: scopeOfUse) {
        result.append(.init(d, at: program[n].site))
      }
    }
    return result
  }

  /// Returns the origins of the conformances of `model` to `trait` that are declared in extensions
  /// exposed to `scopeOfUse`.
  private mutating func originsOfConformance(
    to trait: TraitType, declaredInExtensionsOf model: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> [ConformanceOrigin] {
    var result: [ConformanceOrigin] = []
    for e in extensions(of: model, exposedTo: scopeOfUse) {
      guard let d = ConformanceDecl.ID(e) else { continue }
      let s = originsOfConformance(to: trait, declaredBy: d, exposedTo: scopeOfUse)
      result.append(contentsOf: s)
    }
    return result
  }

  /// Returns the type implementing `requirement` for `model` in `scopeOfUse`, or `nil` if `model`
  /// does not implement `requirement`.
  private mutating func demandImplementation(
    of requirement: AssociatedTypeDecl.ID, for model: AnyType, in scopeOfUse: AnyScopeID
  ) -> AnyType? {
    let p = traitDeclaring(requirement)!
    let m = canonical(model, in: scopeOfUse)

    if let c = demandConformance(of: m, to: p, exposedTo: scopeOfUse) {
      return demandImplementation(of: requirement, in: c)
    } else if m.base is GenericTypeParameterType {
      return ^AssociatedTypeType(requirement, domain: m, ast: program.ast)
    } else {
      return nil
    }
  }

  /// Returns the type implementing requirement `r` in conformance `c` if `c` is well-formed.
  private mutating func demandImplementation(
    of r: AssociatedTypeDecl.ID, in c: Conformance
  ) -> AnyType? {
    let t = uncheckedType(of: c.implementations[r]!.decl!)
    return MetatypeType(t).map { (a) in
      specialize(a.instance, for: c.arguments, in: c.scope)
    }
  }

  // MARK: Type transformations

  /// Returns `generic` with occurrences of parameters keying `specialization` replaced by their
  /// corresponding value, performing necessary name lookups from `scopeOfUse`.
  ///
  /// This method has no effect if `specialization` is empty.
  mutating func specialize(
    _ generic: AnyType, for specialization: GenericArguments, in scopeOfUse: AnyScopeID
  ) -> AnyType {
    return specialization.isEmpty ? generic : generic.transform(mutating: &self, transform)

    func transform(mutating me: inout Self, _ t: AnyType) -> TypeTransformAction {
      switch t.base {
      case let u as AssociatedTypeType:
        return .stepOver(transform(mutating: &me, u))
      case let u as BoundGenericType:
        return .stepOver(transform(mutating: &me, u))
      case let u as GenericTypeParameterType:
        return .stepOver(transform(mutating: &me, u))
      case let u as ProductType:
        return .stepOver(transform(mutating: &me, u, declaredBy: u.decl))
      case let u as TypeAliasType:
        return .stepOver(transform(mutating: &me, u))
      default:
        return .stepInto(t)
      }
    }

    func transform(mutating me: inout Self, _ t: AssociatedTypeType) -> AnyType {
      let d = t.domain.transform(mutating: &me, transform)

      // There's nothing to do if `d` is a trait receiver or another associated type. The latter
      // case happens if we have `T.X.Y` where `T` is a trait receiver.
      if me.isAbstractAssociatedDomain(d) {
        return ^AssociatedTypeType(t.decl, domain: d, ast: me.program.ast)
      }

      // DR: Maybe we could use `d`'s conformance if it has already been established.

      // Otherwise, look for the member of the domain that implements the associated type.
      var candidates = me.lookup(me.program[t.decl].baseName, memberOf: d, exposedTo: scopeOfUse)

      // Ignore associated type declaration unless they define a default value that isn't
      // overridden in the conforming type.
      if let i = candidates.firstIndex(where: { $0.kind == AssociatedTypeDecl.self }) {
        if candidates.count > 1 {
          candidates.remove(at: i)
        } else if let a = me.program[AssociatedTypeDecl.ID(candidates[i])!].defaultValue {
          return me.evalTypeAnnotation(a)
        }
      }

      if let s = candidates.uniqueElement, let u = MetatypeType(me.uncheckedType(of: s)) {
        if let b = BoundGenericType(me.canonical(d, in: scopeOfUse)) {
          return me.specialize(u.instance, for: .init(b), in: scopeOfUse)
        } else {
          return u.instance
        }
      }

      return .error
    }

    func transform(mutating me: inout Self, _ t: BoundGenericType) -> AnyType {
      let b: AnyType

      switch t.base.base {
      case is ProductType:
        b = t.base
      case let u as TypeAliasType:
        let aliasee = u.aliasee.value.transform(mutating: &me, transform)
        b = ^TypeAliasType(aliasing: aliasee, declaredBy: u.decl, in: me.program.ast)
      default:
        b = t.base.transform(mutating: &me, transform)
      }

      let a = t.arguments.mapValues { (v) in
        let w = v.asType ?? UNIMPLEMENTED("generic value arguments")
        return CompileTimeValue.type(w.transform(mutating: &me, transform))
      }
      return ^BoundGenericType(b, arguments: a)
    }

    func transform(mutating me: inout Self, _ t: GenericTypeParameterType) -> AnyType {
      if let v = specialization[t.decl] {
        return v.asType ?? preconditionFailure("expected type")
      } else {
        return ^t
      }
    }

    func transform(mutating me: inout Self, _ t: TypeAliasType) -> AnyType {
      let u = t.aliasee.value.transform(mutating: &me, transform)
      return transform(
        mutating: &me,
        TypeAliasType(aliasing: u, declaredBy: t.decl, in: me.program.ast), declaredBy: t.decl)
    }

    /// If `t` is an unspecialized generic type, returns a bound generic type applying that applies
    /// `substitution` and maps unbound parameters to fresh variables. Otherwise, returns `t`.
    ///
    /// - Requires: `t` is not a trait.
    func transform<T: TypeProtocol, D: GenericScope>(
      mutating me: inout Self, _ t: T, declaredBy d: D.ID
    ) -> AnyType {
      assert(!(t is TraitType))
      let parameters = me.program[d].genericParameters
      if parameters.isEmpty {
        return ^t
      }

      var a: BoundGenericType.Arguments = [:]
      for p in parameters {
        a[p] = specialization[p] ?? .type(^me.freshVariable())
      }
      return ^BoundGenericType(t, arguments: a)
    }
  }

  /// Returns the type checking constraint that specializes `generic` for `specialization` in
  /// `scopeOfUse`, anchoring it at `origin`.
  private mutating func specialize(
    _ generic: GenericConstraint, for specialization: GenericArguments, in scopeOfUse: AnyScopeID,
    origin: ConstraintOrigin
  ) -> Constraint {
    switch generic.value {
    case .conformance(let lhs, let rhs):
      let a = specialize(lhs, for: specialization, in: scopeOfUse)
      return ConformanceConstraint(a, conformsTo: rhs, origin: origin)

    case .equality(let lhs, let rhs):
      let a = specialize(lhs, for: specialization, in: scopeOfUse)
      let b = specialize(rhs, for: specialization, in: scopeOfUse)
      return EqualityConstraint(a, b, origin: origin)

    case .instance, .predicate:
      UNIMPLEMENTED()
    }
  }

  /// Returns the type declared by `d` with its generic parameters bound to fresh variables.
  ///
  /// - Requires: `d` is a a generic product type or type alias declaration.
  mutating func openForUnification(_ d: AnyDeclID) -> BoundGenericType {
    let parameters: [GenericParameterDecl.ID]
    if let t = ProductTypeDecl.ID(d) {
      parameters = program[t].genericClause!.value.parameters
    } else if let t = TypeAliasDecl.ID(d) {
      parameters = program.ast[t].genericClause!.value.parameters
    } else {
      preconditionFailure()
    }

    let b = MetatypeType(uncheckedType(of: d))!.instance
    var a: BoundGenericType.Arguments = [:]
    for p in parameters {
      a[p] = .type(^freshVariable())
    }
    return BoundGenericType(b, arguments: a)
  }

  // MARK: Type checking

  /// Applies all pending updates to the shared instance.
  mutating func synchronize() {
    cache.synchronize()
  }

  /// Type checks all declarations in `self.program`.
  mutating func checkAllDeclarations() {
    check(program.ast.modules)
  }

  /// Type checks `m`.
  mutating func checkModule(_ m: ModuleDecl.ID) {
    check(m)
  }

  /// Type checks the sources in `batch`.
  mutating func check<S: Sequence<TranslationUnit.ID>>(_ batch: S) {
    for u in batch { check(u) }
  }

  /// Type checks `u` and all declarations nested in `d`.
  private mutating func check(_ u: TranslationUnit.ID) {
    _ = imports(exposedTo: u)
    check(program[u].decls)
  }

  /// Type checks the declarations in `batch`.
  private mutating func check<S: Sequence<T>, T: DeclID>(
    _ batch: S, ignoringSharedCache ignoreSharedCache: Bool = false
  ) {
    for d in batch { check(d, ignoringSharedCache: ignoreSharedCache) }
  }

  /// Type checks `d` and all declarations nested in `d`.
  ///
  /// Type checking is performed if and only if `cache[\.declType][d]` is `nil`. In this case, the
  /// type of `d` is computed with `uncheckedType(of: d)` and assigned to `cache[\.declType][d]`
  /// before type checking. Then, `_check(d)` is called with `cache.declsUnderChecking` containing
  /// `d`. After the call, `cache.declsUnderChecking` doesn't contain `d`. A diagnostic is reported
  /// if type checking failed.
  ///
  /// Type checking typically consists of visiting a declaration to generate proof obligations that
  /// are then discharged by solving type constraints and/or type checking additional declarations.
  ///
  /// - Parameters:
  ///   - d: The declaration to type check.
  ///
  /// - Requires: `!cache.declsUnderChecking.contains(d)`
  private mutating func check<T: DeclID>(
    _ d: T, ignoringSharedCache ignoreSharedCache: Bool = false
  ) {
    // Handle binding declarations as a special case.
    if let b = BindingDecl.ID(d) {
      checkedType(of: b, ignoringSharedCache: ignoreSharedCache)
      return
    }

    // Check if work has to be done.
    if cache.read(\.declType[d], ignoringSharedCache: ignoreSharedCache) != nil { return }

    // Prepare the declaration for type checking.
    let t = uncheckedType(of: d, ignoringSharedCache: ignoreSharedCache)
    if t.isError {
      cache.write(.error, at: \.declType[d], ignoringSharedCache: ignoreSharedCache)
      return
    }

    // Check for infinite recursion.
    if !cache.declsUnderChecking.insert(AnyDeclID(d)).inserted {
      fatalError("infinite recursion caused by '\(d.kind)' at \(program[d].site)")
    }

    // Do the work.
    switch d.kind {
    case AssociatedTypeDecl.self:
      break
    case AssociatedValueDecl.self:
      break
    case ConformanceDecl.self:
      _check(ConformanceDecl.ID(d)!)
    case ExtensionDecl.self:
      _check(ExtensionDecl.ID(d)!)
    case FunctionDecl.self:
      _check(FunctionDecl.ID(d)!, ignoringSharedCache: ignoreSharedCache)
    case GenericParameterDecl.self:
      _check(GenericParameterDecl.ID(d)!)
    case ImportDecl.self:
      break
    case InitializerDecl.self:
      _check(InitializerDecl.ID(d)!)
    case MethodDecl.self:
      _check(MethodDecl.ID(d)!)
    case MethodImpl.self:
      _check(MethodImpl.ID(d)!)
    case ModuleDecl.self:
      _check(ModuleDecl.ID(d)!)
    case NamespaceDecl.self:
      _check(NamespaceDecl.ID(d)!)
    case OperatorDecl.self:
      _check(OperatorDecl.ID(d)!)
    case ParameterDecl.self:
      _check(ParameterDecl.ID(d)!)
    case ProductTypeDecl.self:
      _check(ProductTypeDecl.ID(d)!)
    case SubscriptDecl.self:
      _check(SubscriptDecl.ID(d)!)
    case SubscriptImpl.self:
      _check(SubscriptImpl.ID(d)!)
    case TraitDecl.self:
      _check(TraitDecl.ID(d)!)
    case TypeAliasDecl.self:
      _check(TypeAliasDecl.ID(d)!)
    default:
      unexpected(d, in: program.ast)
    }

    // Commit result to the cache.
    cache.declsUnderChecking.remove(AnyDeclID(d))
    cache.write(t, at: \.declType[d], ignoringSharedCache: ignoreSharedCache)
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: ConformanceDecl.ID) {
    checkEnvironment(of: d)
    checkAllConformances(declaredBy: d)
    check(program[d].members)
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: ExtensionDecl.ID) {
    checkEnvironment(of: d)
    check(program[d].members)
  }

  /// Type checks `d` and all declarations nested in `d`.
  ///
  /// - Requires: `d` is not the underlying declaration of a lambda.
  private mutating func _check(_ d: FunctionDecl.ID, ignoringSharedCache ignoreSharedCache: Bool) {
    checkEnvironment(of: d)
    checkParameters(program[d].parameters, of: d)

    let a = FunctionAttributes(
      externalName: program[d].isExternal ? program.ast.externalName(of: d) : nil,
      foreignName: program[d].isForeignInterface ? program.ast.foreignName(of: d) : nil)
    cache.write(a, at: \.functionAttributes[d], ignoringSharedCache: ignoreSharedCache)

    switch program[d].body {
    case .block(let b):
      check(b)

    case .expr(let b):
      let r = ArrowType(uncheckedType(of: d))!.output
      check(b, asBodyOfCallableProducing: r)

    case nil:
      // Only requirements, FFIs, and external functions can be without a body.
      if requiresBody(d) {
        report(.error(declarationRequiresBodyAt: program[d].introducerSite))
      }
    }
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: GenericParameterDecl.ID) {
    // TODO: Type check default values
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: InitializerDecl.ID) {
    // Memberwize initializers trivially type check.
    if program[d].isMemberwise { return }

    // Note: receiver is type checked in `_uncheckedType(of:)`.
    checkEnvironment(of: d)
    checkParameters(program[d].parameters, of: d)

    if let b = program[d].body {
      check(b)
    } else if !program.isRequirement(d) {
      report(.error(declarationRequiresBodyAt: program[d].introducer.site))
    }
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: MethodDecl.ID) {
    checkEnvironment(of: d)
    checkParameters(program[d].parameters, of: d)
    check(program[d].impls)
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: MethodImpl.ID) {
    let t = MethodType(uncheckedType(of: MethodDecl.ID(program[d].scope)!))!
    cache.write(
      ^ParameterType(program[d].introducer.value, t.receiver),
      at: \.declType[program[d].receiver])

    switch program[d].body {
    case .block(let b):
      check(b)

    case .expr(let b):
      let r = ArrowType(uncheckedType(of: d))!.output
      check(b, asBodyOfCallableProducing: r)

    case nil:
      if !program.isRequirement(d) {
        report(.error(declarationRequiresBodyAt: program[d].introducer.site))
      }
    }
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: ModuleDecl.ID) {
    check(program[d].sources)
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: NamespaceDecl.ID) {
    check(program[d].members)
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: OperatorDecl.ID) {
    let s = TranslationUnit.ID(program[d].scope)!
    for o in program[s].decls where o.kind == OperatorDecl.self {
      let other = OperatorDecl.ID(o)!
      if o != d,
        program[other].notation.value == program[d].notation.value,
        program[other].name.value == program[d].name.value
      {
        report(.error(duplicateOperatorNamed: program[d].name.value, at: program[d].site))
      }
    }
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: ParameterDecl.ID) {
    if let e = program[d].defaultValue {
      guard let p = uncheckedType(of: d).errorFree else { return }
      _ = checkedType(of: e, asArgumentTo: ParameterType(p)!)

      var w = RecursiveReferenceRecognizer(
        targets: program.siblings(of: d), referredDecl: cache.local.referredDecl)
      program.ast.walk(e, notifying: &w)
      for r in w.recursiveReferences {
        report(.error(referenceToSibling: r, in: program.ast))
      }
    }
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: ProductTypeDecl.ID) {
    checkEnvironment(of: d)
    checkAllConformances(declaredBy: d)
    check(program[d].members)
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: SubscriptDecl.ID) {
    checkEnvironment(of: d)
    checkParameters(program[d].parameters, of: d)
    check(program[d].impls)
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: SubscriptImpl.ID) {
    if let r = program[d].receiver {
      let t = SubscriptType(uncheckedType(of: SubscriptDecl.ID(program[d].scope)!))!
      let u = RemoteType(t.captures[0].type)!
      cache.write(
        ^ParameterType(program[d].introducer.value, u.bareType),
        at: \.declType[r])
    }

    switch program[d].body {
    case .block(let b):
      check(b)

    case .expr(let b):
      let r = SubscriptImplType(uncheckedType(of: d))!.output
      check(b, asBodyOfCallableProducing: r)

    case nil:
      if !program.isRequirement(d) {
        report(.error(declarationRequiresBodyAt: program[d].introducer.site))
      }
    }
  }

  /// Type checks `d` and all declarations nested in `d`.
  private mutating func _check(_ d: TraitDecl.ID) {
    checkEnvironment(of: d)
    check(program[d].members)
    check(extensions(of: uncheckedType(of: d), exposedTo: program[d].scope))
  }

  private mutating func _check(_ d: TypeAliasDecl.ID) {
    checkEnvironment(of: d)
    let aliased = MetatypeType(uncheckedType(of: d))!.instance

    for e in extensions(of: aliased, exposedTo: program[d].scope) {
      // The alias may be referring to the type being declared by a scope containing `d`, in which
      // case type checking `e` may trigger infinite recursion.
      if cache.declsUnderChecking.contains(e) { continue }
      check(e)
    }
  }

  /// Type checks the parameters `ps` of `d`.
  ///
  /// - Requires: The parameters in `ps` have type annotations.
  private mutating func checkParameters<T: Decl & LexicalScope>(
    _ ps: [ParameterDecl.ID], of d: T.ID
  ) {
    var siblings = Set<String>()
    for p in ps {
      if siblings.insert(program[p].baseName).inserted {
        check(p)
      } else {
        report(.error(duplicateParameterNamed: program[p].baseName, at: program[p].site))
        cache.write(.error, at: \.declType[p])
      }
    }
  }

  /// Type checks `d` after its type has been inferred.
  ///
  /// This method is called from `discharge(obligations:relatedTo:)` on declarations whose types
  /// appear in the obligations to discharge.
  ///
  /// - Requires: `cache.uncheckedType[d]` has been computed.
  private mutating func checkPostInference<T: DeclID>(
    _ d: T, solution: Solution, ignoringSharedCache ignoreSharedCache: Bool
  ) {
    // Prepare the declaration for type checking.
    let t = reifyUncheckedType(of: d, withAssignmentsIn: solution)
    if t.isError {
      cache.write(.error, at: \.declType[d], ignoringSharedCache: ignoreSharedCache)
      return
    }

    switch d.kind {
    case FunctionDecl.self:
      checkPostInference(FunctionDecl.ID(d)!, solution: solution)
    case VarDecl.self:
      cache.write(t, at: \.declType[d], ignoringSharedCache: ignoreSharedCache)
    default:
      unexpected(d, in: program.ast)
    }
  }

  /// Type checks `d`, which declares a lambda, after its type has been inferred.
  private mutating func checkPostInference(_ d: FunctionDecl.ID, solution: Solution) {
    assert(program[d].isInExprContext, "expected lambda")
    for c in program[d].explicitCaptures {
      reifyUncheckedType(of: c, withAssignmentsIn: solution)
    }
    for p in program[d].parameters {
      reifyUncheckedType(of: p, withAssignmentsIn: solution)
    }
    check(d, ignoringSharedCache: true)
  }

  /// Substitutes open variables occurring in `cache.uncheckedType[d]` with their corresponding
  /// assignment in `solution`, returning `d`'s reified type.
  ///
  /// - Requires: `cache.uncheckedType[d]` has been computed.
  @discardableResult
  private mutating func reifyUncheckedType<T: DeclID>(
    of d: T, withAssignmentsIn solution: Solution
  ) -> AnyType {
    // Note: in theory, we should make sure this update is monotonic. In practice, such a test
    // would require prohibitively expensive structural comparisons.
    modify(&cache.uncheckedType[d]!) { (u) in
      let v = solution.substitutions.reify(u.computed!)
      u = .computed(v)
      return v
    }
  }

  /// Type checks `e` as the body of a function returning or susbscript projecting `r`.
  private mutating func check(_ e: AnyExprID, asBodyOfCallableProducing r: AnyType) {
    var obligations = ProofObligations(scope: program[e].scope)
    let body = inferredType(of: e, withHint: r, updating: &obligations)

    // Inline functions may return `Never` regardless of their return type.
    let o = ConstraintOrigin(.return, at: program[e].site)
    let equalToNever = EqualityConstraint(body, .never, origin: o)

    if areEquivalent(r, .never, in: program[e].scope) {
      obligations.insert(equalToNever)
    } else {
      let equalToOutput = EqualityConstraint(body, r, origin: o)
      let equalToOutputOrNever = DisjunctionConstraint(
        between: [
          .init(constraints: [equalToOutput], penalties: 0),
          .init(constraints: [equalToNever], penalties: 1),
        ],
        origin: o)
      obligations.insert(equalToOutputOrNever)
    }

    discharge(obligations, relatedTo: e)
  }

  /// Checks that `e` is an instance of `t`.
  private mutating func check(_ e: AnyExprID, instanceOf t: AnyType) {
    var obligations = ProofObligations(scope: program[e].scope)
    let u = inferredType(of: e, withHint: t, updating: &obligations)
    obligations.insert(
      EqualityConstraint(t, u, origin: .init(.structural, at: program[e].site)))
    discharge(obligations, relatedTo: e)
  }

  /// Type checks `s`.
  private mutating func check<T: StmtID>(_ s: T) {
    switch s.kind {
    case AssignStmt.self:
      check(AssignStmt.ID(s)!)
    case BraceStmt.self:
      check(BraceStmt.ID(s)!)
    case BreakStmt.self:
      break
    case ConditionalBindingStmt.self:
      check(ConditionalBindingStmt.ID(s)!)
    case ConditionalCompilationStmt.self:
      check(ConditionalCompilationStmt.ID(s)!)
    case ConditionalStmt.self:
      check(ConditionalStmt.ID(s)!)
    case ContinueStmt.self:
      break
    case ExprStmt.self:
      check(ExprStmt.ID(s)!)
    case DeclStmt.self:
      check(DeclStmt.ID(s)!)
    case DiscardStmt.self:
      check(DiscardStmt.ID(s)!)
    case DoWhileStmt.self:
      check(DoWhileStmt.ID(s)!)
    case ForStmt.self:
      check(ForStmt.ID(s)!)
    case ReturnStmt.self:
      check(ReturnStmt.ID(s)!)
    case WhileStmt.self:
      check(WhileStmt.ID(s)!)
    case YieldStmt.self:
      check(YieldStmt.ID(s)!)
    default:
      unexpected(s, in: program.ast)
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: BraceStmt.ID) {
    for t in program[s].stmts { check(t) }
  }

  /// Type checks `s`.
  private mutating func check(_ s: AssignStmt.ID) {
    var obligations = ProofObligations(scope: program[s].scope)
    let o = ConstraintOrigin(.initializationOrAssignment, at: program[s].site)

    // `lhs` must be `Movable`.
    let lhs = inferredType(of: program[s].left, updating: &obligations)
    obligations.insert(
      ConformanceConstraint(lhs, conformsTo: program.ast.core.movable.type, origin: o))

    // `rhs` must be equal of `lhs`.
    let rhs = inferredType(
      of: program[s].right, withHint: lhs, updating: &obligations)
    obligations.insert(EqualityConstraint(rhs, lhs, origin: o))

    discharge(obligations, relatedTo: s)
  }

  /// Type checks `s`.
  private mutating func check(_ s: ConditionalBindingStmt.ID) {
    checkedType(of: program[s].binding, usedAs: .condition, ignoringSharedCache: true)

    let f = program.ast[s].fallback
    check(f)

    if canFallThrough(f) {
      let site = program[f].stmts.last.map({ (l) in program[l].site }) ?? program[f].site
      report(.error(fallbackBranchCannotFallThroughAt: site))
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: ConditionalCompilationStmt.ID) {
    for t in program.ast[s].expansion(for: program.ast.compilationConditions) { check(t) }
  }

  /// Type checks `s`.
  private mutating func check(_ s: ConditionalStmt.ID) {
    check(program[s].condition)
    check(program[s].success)
    if let b = program[s].failure {
      check(b.value)
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: ExprStmt.ID) {
    guard let result = checkedType(of: program[s].expr).errorFree else { return }

    // Warn against unused result if the type of the expression is neither `Void` nor `Never`.
    let t = canonical(result, in: program[s].scope)
    if !t.isVoidOrNever {
      report(.warning(unusedResultOfType: result, at: program[s].expr.site))
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: DeclStmt.ID) {
    check(program[s].decl)
  }

  /// Type checks `s`.
  private mutating func check(_ s: DiscardStmt.ID) {
    var obligations = ProofObligations(scope: program[s].scope)
    let t = inferredType(of: program[s].expr, updating: &obligations)

    // Expression must be `Deinitializable`.
    obligations.insert(
      ConformanceConstraint(
        t, conformsTo: program.ast.core.deinitializable.type,
        origin: .init(.discard, at: program[s].site)))

    discharge(obligations, relatedTo: s)
  }

  /// Type checks `s`.
  private mutating func check(_ s: DoWhileStmt.ID) {
    check(program[s].body)
    check(program[s].condition.value, instanceOf: ^program.ast.coreType("Bool")!)
  }

  /// Type checks `s`.
  private mutating func check(_ s: ForStmt.ID) {
    guard let element = inferredIterationElementType(of: s) else { return }

    let e = checkedType(of: program[s].binding, usedAs: .filter(matching: element))
    checkedType(of: program[s].binding, usedAs: .filter(matching: e), ignoringSharedCache: true)
    if let e = program[s].filter {
      check(e.value, instanceOf: ^program.ast.coreType("Bool")!)
    }
    check(program[s].body)
  }

  /// Type checks `s`.
  private mutating func check(_ s: ReturnStmt.ID) {
    let output = uncheckedOutputType(in: program[s].scope)!

    if let v = program[s].value {
      check(v, instanceOf: output)
    } else if !areEquivalent(output, .void, in: program[s].scope) {
      report(.error(missingReturnValueAt: program[s].site))
    }
  }

  /// Type checks `s`.
  private mutating func check(_ s: WhileStmt.ID) {
    check(program[s].condition)
    check(program[s].body)
  }

  /// Type checks `s`.
  private mutating func check(_ s: YieldStmt.ID) {
    let output = uncheckedOutputType(in: program[s].scope)!
    check(program[s].value, instanceOf: output)
  }

  /// Type checks `condition`.
  private mutating func check(_ condition: [ConditionItem]) {
    let bool = ^program.ast.coreType("Bool")!
    for item in condition {
      switch item {
      case .expr(let e):
        check(e, instanceOf: bool)
      case .decl(let d):
        checkedType(of: d, usedAs: .condition, ignoringSharedCache: true)
      }
    }
  }

  /// Returns the modules visible as imports in `u`.
  ///
  /// The returned set contains the modules declared as explicit imports at the top of `u` along
  /// with the standard library and the module containing `u`.
  private mutating func imports(exposedTo u: TranslationUnit.ID) -> Set<ModuleDecl.ID> {
    if let result = cache.read(\.imports[u]) {
      return result
    }

    // The core library and the containing module are always implicitly imported.
    var result: Set<ModuleDecl.ID> = [ModuleDecl.ID(program[u].scope)!]
    if let m = program.ast.coreLibrary {
      result.insert(m)
    }

    for d in program[u].decls {
      if let i = ImportDecl.ID(d) { insertImport(i, from: u, in: &result) }
    }

    cache.write(result, at: \.imports[u])
    return result
  }

  /// If `d` is a valid import in `u`, inserts the module referred by `d` in `imports`; reports a
  /// diagnostic otherwise.
  private mutating func insertImport(
    _ d: ImportDecl.ID, from u: TranslationUnit.ID, in imports: inout Set<ModuleDecl.ID>
  ) {
    guard let m = ModuleType(uncheckedType(of: d)) else { return }

    if program.module(containing: u) != m.decl {
      imports.insert(m.decl)
    } else {
      report(.warning(needlessImport: d, in: program.ast))
    }
  }

  /// Builds and type checks the generic environment of `d`.
  private mutating func checkEnvironment<T: GenericDecl & LexicalScope>(of d: T.ID) {
    // TODO: Type check default values
    let e = environment(of: d)
    check(program[d].genericParameters)
    if let f = shouldLogRequirementSystem, f(AnyDeclID(d), program) {
      print(program.describe(e.requirements))
    }
  }

  /// Builds and type checks the generic environment of `d`.
  private mutating func checkEnvironment(of d: TraitDecl.ID) {
    // TODO: Type check default values
    let e = environment(of: d)
    check(program[d].genericParameters)
    if let f = shouldLogRequirementSystem, f(AnyDeclID(d), program) {
      print(program.describe(e.requirements))
    }
  }

  /// Builds and type checks the generic environment of `d`.
  private mutating func checkEnvironment<T: TypeExtendingDecl>(of d: T.ID) {
    // TODO: Type check default values
    let e = environment(of: d)
    if let f = shouldLogRequirementSystem, f(AnyDeclID(d), program) {
      print(program.describe(e.requirements))
    }
  }

  /// Type checks the conformances declared by `d`.
  ///
  /// Only well-typed conformances are added to `self.conformances`. A diagnostic is reported for
  /// each ill-typed conformance.
  private mutating func checkAllConformances<T: ConformanceSource>(declaredBy d: T.ID) {
    for (_, rhs) in evalTraitComposition(program[d].conformances) {
      let r = bases(of: rhs)
      checkConformances(to: r, declaredBy: AnyDeclID(d))
    }
  }

  /// Type checks the conformances to `traits` declared by `d`.
  ///
  /// - Parameters:
  ///   - traits: A refinement closure for one of the traits mentioned by `d`. For instance, if `d`
  ///     is a type declaration `type A: P, Q {}`, `traits` is a closure describing the refinements
  ///     of either `P` or `Q`.
  ///   - d: A conformance source.
  private mutating func checkConformances(to traits: RefinementClosure, declaredBy d: AnyDeclID) {
    precondition(d.isConformanceSource)

    let scopeOfDefinition = program[d].scope
    let m = canonical(extendedModel(d), in: scopeOfDefinition)
    if m[.hasError] { return }

    for t in traits.orderedByDependency {
      let s = originsOfConformance(of: m, to: t, exposedTo: scopeOfDefinition)
      checkConformance(to: t, declaredBy: s, in: scopeOfDefinition)
    }
  }

  /// Type checks the conformance to `trait` declared by `origins` in `scopeOfDefinition`.
  ///
  /// This method deterministically selects the declaration severing as the origin of a type's
  /// conformance to a specific trait in a scope, reporting diagnostics of ambiguous cases.
  ///
  /// - Parameters:
  ///   - trait: A trait belonging to the refinement closure of a trait mentioned by one of the
  ///     conformance sources in `origins`.
  ///   - origins: The declarations introducing a conformance to `trait` in `scopeOfDefinition`.
  ///   - scopeOfDefinition: The outermost scope in which the conformance is checked.
  ///
  /// - Requires: Conformances to traits strictly refined by `trait` have already been checked.
  private mutating func checkConformance(
    to trait: TraitType, declaredBy origins: [ConformanceOrigin],
    in scopeOfDefinition: AnyScopeID
  ) {
    let s = origins.filter({ (o) in program.isContained(o.source, in: scopeOfDefinition) })

    // TODO: If there exists several conformances, make sure they have the same bounds.

    // We could use a more clever algorithm to select the least refined declaration (e.g., `A: Q`
    // where there are both `A: P` and `A: Q` such that `P` refines `Q`), but all choices have the
    // same semantics. So any criterion is fine as long as we can generate consistent diagnostics
    // when errors occur.
    let o = s.sorted(by: \.source.rawValue).first!
    checkConformance(to: trait, declaredBy: o)
  }

  /// Type checks the conformance to `trait` declared by `origin`.
  ///
  /// - Parameters:
  ///   - trait: A trait belonging to the refinement closure of a trait mentioned `origin`.
  ///   - origin: A declaration introducing a conformance to `trait`.
  ///
  /// - Requires: Conformances to traits strictly refined by `trait` have already been checked.
  private mutating func checkConformance(
    to trait: TraitType, declaredBy origin: ConformanceOrigin
  ) {
    /// The scope in which the origin of the conformance is defined.
    let scopeOfDefinition = program[origin.source].scope

    /// The scope in which the conformance applies.
    ///
    /// Conformances at file scope are exposed in the whole module. Other conformances are exposed
    /// in their containing scope.
    let scopeOfExposition = read(scopeOfDefinition) { (s) in
      (s.kind == TranslationUnit.self) ? program[s].scope : s
    }

    /// The type for which conformance to `trait` is being checked.
    let model = canonical(extendedModel(origin.source), in: scopeOfDefinition)
    if model[.hasError] { return }

    // TODO: Use arguments to bound generic types as constraints

    // There's nothing to do if the conformance introduced by `origin` has already been checked.
    // Otherwise, if there's already another conformance exposed to `scopeOfDefinition` in cache,
    // it can't be introduced the same scope.
    if let c = cachedConformance(of: model, to: trait, exposedTo: scopeOfDefinition) {
      if c.origin == origin {
        return
      } else {
        precondition(c.scope != scopeOfDefinition, "inconsistent conformance origin")
      }
    }

    /// A map from requirement to its implementation.
    var implementations = Conformance.ImplementationMap()

    /// The detailed diagnostics describing why the checked conformance does not hold.
    var nonConformanceNotes = DiagnosticSet()

    /// A map associating the "Self" parameter of each trait to which `model` conforms to `model`.
    var traitReceiverToModel = GenericArguments()
    for t in conformedTraits(of: model, in: scopeOfDefinition) {
      traitReceiverToModel[program[t.decl].receiver] = .type(model)
    }

    for r in program.ast.requirements(of: trait.decl) {
      resolveImplementation(of: r)
    }

    if !nonConformanceNotes.isEmpty || !checkRequirementConstraints() {
      // Use `extendedModel(_:)` to get `model` as it was declared in program sources.
      let m = extendedModel(origin.source)
      report(.error(m, doesNotConformTo: trait, at: origin.site, because: nonConformanceNotes))
      return
    }

    let c = Conformance(
      model: BoundGenericType(model)?.base ?? model, concept: trait,
      arguments: .empty, conditions: [], scope: scopeOfExposition,
      implementations: implementations, isStructural: false, origin: origin)
    insertConformance(c)
    return

    /// The information describing how to refer to and use an entity.
    typealias API = (type: AnyType, name: Name, parameters: [GenericParameterDecl.ID])

    /// Returns the API of `m` viewed as a member of `model` through its conformance to `trait`.
    func canonicaAPI(of m: AnyDeclID) -> API {
      return (
        type: canonical(expectedType(of: m), in: scopeOfDefinition),
        name: program.name(of: m)!,
        parameters: genericParameters(introducedBy: m)
      )
    }

    /// Returns the type of `m` viewed as a member of `model` through its conformance to `trait`.
    func expectedType(of m: AnyDeclID) -> AnyType {
      specialize(uncheckedType(of: m), for: traitReceiverToModel, in: scopeOfDefinition)
    }

    /// Checks whether the constraints on the requirements of `trait` are satisfied by `model` in
    /// `scopeOfuse`, reporting diagnostics in `conformanceDiagnostics`.
    func checkRequirementConstraints() -> Bool {
      let e = environment(of: trait.decl)
      var obligations = ProofObligations(
        scope: AnyScopeID(origin.source) ?? program[origin.source].scope)

      for g in e.constraints {
        let c = specialize(
          g, for: traitReceiverToModel, in: scopeOfDefinition,
          origin: .init(.structural, at: origin.site))
        obligations.insert(c)
      }

      let s = discharge(obligations, relatedTo: origin.source)
      return s.isSound
    }

    /// Identifies the implementation of `requirement` for `model`.
    ///
    /// If an implementation is found, it is written to `implementations`. Otherwise, a diagnostic
    /// is reported in `conformanceDiagnostics`.
    func resolveImplementation(of requirement: AnyDeclID) {
      switch requirement.kind {
      case AssociatedTypeDecl.self:
        return resolveAssociatedImplementation(of: AssociatedTypeDecl.ID(requirement)!)
      case AssociatedValueDecl.self:
        UNIMPLEMENTED("associated values are not supported yet")
      default:
        resolveFunctionalImplementation(of: requirement)
      }
    }

    /// Identifies the implementation of `requirement` for `model`.
    func resolveAssociatedImplementation(of requirement: AssociatedTypeDecl.ID) {
      guard let d = implementation(of: requirement) else {
        let n = Diagnostic.note(
          trait: trait, requiresAssociatedType: program[requirement].baseName, at: origin.site)
        nonConformanceNotes.insert(n)
        return
      }
      implementations[requirement] = .explicit(d)
    }

    /// Identifies the implementation of `requirement` for `model`.
    ///
    /// `requirement` is a function, initializer, or subscript requirement.
    func resolveFunctionalImplementation(of requirement: AnyDeclID) {
      let expectedAPI = canonicaAPI(of: requirement)

      // Look for a user-defined implementation.
      if let d = concreteImplementation(of: requirement, withAPI: expectedAPI) {
        implementations[requirement] = .explicit(d)
      }

      // Build a synthetic implementation if possible.
      else if let d = syntheticImplementation(of: requirement, withAPI: expectedAPI) {
        implementations[requirement] = .synthetic(d)
        registerSynthesizedDecl(d, in: program.module(containing: program[origin.source].scope))
      }

      // No implementation matches the requirement.
      else {
        let t = expectedType(of: requirement)
        let n = Diagnostic.note(
          trait: trait, requires: requirement.kind,
          named: expectedAPI.name, typed: t,
          at: origin.site)
        nonConformanceNotes.insert(n)
      }
    }

    /// Returns a synthetic implementation of `requirement` for `model` with given `expectedAPI`,
    /// or `nil` if no such implementation can be synthesized.
    func syntheticImplementation(
      of requirement: AnyDeclID, withAPI expectedAPI: API
    ) -> SynthesizedFunctionDecl? {
      let scopeOfImplementation = AnyScopeID(origin.source)!
      if let k = program.ast.synthesizedKind(of: requirement),
        canSynthesizeConformance(model, to: trait, in: scopeOfImplementation)
      {
        let t = ArrowType(expectedAPI.type)!
        let h = Array(t.environment.skolems)

        // Note: compiler-known requirement is assumed to be well-typed.
        return .init(k, typed: t, parameterizedBy: h, in: scopeOfImplementation)
      } else {
        return nil
      }
    }

    /// Returns a concrete implementation of `requirement` for `model` with given `expectedAPI`,
    /// or `nil` if no such implementation exists.
    func concreteImplementation(
      of requirement: AnyDeclID, withAPI expectedAPI: API
    ) -> AnyDeclID? {
      if expectedAPI.type[.hasError] { return nil }

      switch requirement.kind {
      case FunctionDecl.self:
        return implementation(
          of: requirement, withAPI: expectedAPI,
          collectingCandidatesWith: appendFunctionDefinitions)

      case InitializerDecl.self:
        return implementation(
          of: requirement, withAPI: expectedAPI, identifiedBy: InitializerDecl.ID.self,
          collectingCandidatesWith: appendIfDefinition)

      case MethodImpl.self:
        return implementation(
          of: requirement, withAPI: expectedAPI,
          collectingCandidatesWith: appendFunctionDefinitions)

      case SubscriptImpl.self:
        return implementation(
          of: requirement, withAPI: expectedAPI, identifiedBy: SubscriptDecl.ID.self,
          collectingCandidatesWith: appendDefinitions)

      default:
        unexpected(requirement, in: program.ast)
      }
    }

    /// Returns the implementation of `requirement` in `model` or `nil` if there's none.
    func implementation(of requirement: AssociatedTypeDecl.ID) -> AnyDeclID? {
      let n = program[requirement].baseName
      let candidates = lookup(n, memberOf: model, exposedTo: scopeOfDefinition)

      // Candidates are viable iff they declare a metatype and have a definition.
      let viable: [AnyDeclID] = candidates.reduce(into: []) { (s, c) in
        if !(uncheckedType(of: c).base is MetatypeType) { return }
        if let d = AssociatedTypeDecl.ID(c), program[d].defaultValue == nil { return }
        s.append(c)
      }

      return uniqueViableCandidate(in: viable)
    }

    /// Returns the implementation of `requirement` in `model` or `nil` if there's none.
    ///
    /// - Parameters:
    ///   - expectedAPI: The API `requirement` is expected to have when implemented by `model`.
    ///   - idKind: The kind of declarations to be considered as candidates.
    ///   - appendDefinitions: A closure called for each candidate in the declaration space of
    ///     `model` to gather those that are definitions (i.e., declarations with a body) of an
    ///     entity with the given `expectedAPI`.
    func implementation<D: DeclID>(
      of requirement: AnyDeclID, withAPI expectedAPI: API,
      identifiedBy idKind: D.Type = D.self,
      collectingCandidatesWith appendDefinitions: (D, API, inout [AnyDeclID]) -> Void
    ) -> AnyDeclID? {
      let candidates = lookup(expectedAPI.name.stem, memberOf: model, exposedTo: scopeOfDefinition)
      var viable: [AnyDeclID] = []
      for c in candidates {
        guard let d = D(c) else { continue }
        appendDefinitions(d, expectedAPI, &viable)
      }

      viable = viable.minimalElements(by: { (a, b) in compareDepth(a, b, in: scopeOfDefinition) })
      return uniqueViableCandidate(in: viable)
    }

    /// Returns the contents of `candidates` if it contains a single declaration, reporting a
    /// diagnostic if it doesn't have the right visibility. Otherwise, returns `nil`.
    func uniqueViableCandidate(in candidates: [AnyDeclID]) -> AnyDeclID? {
      guard let pick = candidates.uniqueElement else { return nil }
      if !program.isAccessibleAsRequirementImplementation(pick) {
        nonConformanceNotes.insert(.note(implementationMustBePublic: pick, in: program.ast))
      }
      return pick
    }

    /// Appends the function definitions of `d` that have API `a` to `s` .
    func appendFunctionDefinitions(of d: AnyDeclID, matching a: API, to s: inout [AnyDeclID]) {
      switch d.kind {
      case FunctionDecl.self:
        appendIfDefinition(FunctionDecl.ID(d)!, matching: a, to: &s)
      case MethodDecl.self:
        appendDefinitions(of: MethodDecl.ID(d)!, matching: a, to: &s)
      default:
        break
      }
    }

    /// Appends each variant of `d` that is has API `a` to `s`.
    func appendDefinitions(of d: MethodDecl.ID, matching a: API, to s: inout [AnyDeclID]) {
      for v in program[d].impls { appendIfDefinition(v, matching: a, to: &s) }
    }

    /// Appends each variant of `d` that is has API `a` to `s`.
    func appendDefinitions(of d: SubscriptDecl.ID, matching a: API, to s: inout [AnyDeclID]) {
      for v in program[d].impls { appendIfDefinition(v, matching: a, to: &s) }
    }

    /// Appends `d` to `s` iff `d` is a definition with with API `a`.
    func appendIfDefinition<D: Decl>(_ d: D.ID, matching a: API, to s: inout [AnyDeclID]) {
      let b = canonicaAPI(of: AnyDeclID(d))

      // A generic requirement must be implemented by a generic implementation whose environment
      // implies that of the requirement.
      let expectedType: AnyType

      if a.parameters.isEmpty {
        expectedType = a.type
      } else if a.parameters.count == b.parameters.count {
        var s = GenericArguments()
        for (p, t) in zip(a.parameters, b.parameters) {
          s[p] = .type(^GenericTypeParameterType(t, ast: program.ast))
        }
        expectedType = specialize(a.type, for: s, in: scopeOfDefinition)
      } else {
        return
      }

      assert(expectedType.isCanonical && b.type.isCanonical)
      // TODO: Use semantic equality
      if program[d].isDefinition && (b.type == expectedType) {
        s.append(AnyDeclID(d))
      }
    }
  }

  /// Registers conformance `c` iff it hasn't been established.
  ///
  /// - Note: This method doesn't write to the shared cache.
  private mutating func insertConformance(_ c: Conformance) {
    var traitToConformance = cache.local.conformances[c.model, default: [:]]
    let inserted = modify(&traitToConformance[c.concept, default: []]) { (s) in
      if !s.contains(where: { program.areOverlapping($0.scope, c.scope) }) {
        let i = s.insert(c).inserted
        assert(i)
        return true
      } else {
        return false
      }
    }

    if inserted {
      cache.write(traitToConformance, at: \.conformances[c.model], ignoringSharedCache: true)
    }
  }

  /// Registers the use of synthesized declaration `d` in `m`.
  private mutating func registerSynthesizedDecl(
    _ d: SynthesizedFunctionDecl, in m: ModuleDecl.ID
  ) {
    var s = cache.local.synthesizedDecls[m] ?? []
    s.insert(d)
    cache.write(s, at: \.synthesizedDecls[m], ignoringSharedCache: true)
  }

  /// Type checks `d` and all declarations nested in `d`, returning the type of `d`.
  ///
  /// - Requires: `!cache.declsUnderChecking.contains(d)`
  @discardableResult
  private mutating func checkedType(
    of d: BindingDecl.ID,
    usedAs purpose: BindingDeclUse = .irrefutable,
    ignoringSharedCache ignoreSharedCache: Bool = false
  ) -> AnyType {
    // Check if work has to be done.
    if let t = cache.read(\.declType[d], ignoringSharedCache: ignoreSharedCache) {
      return t
    }

    // Check for infinite recursion.
    if !cache.declsUnderChecking.insert(AnyDeclID(d)).inserted {
      fatalError("infinite recursion")
    }

    // The variable declarations nested in `d` are added to the set of declarations under checking
    // so that name resolution cannot bind a name to itself.
    var names = Set<AnyDeclID>()
    for (_, n) in program.ast.names(in: program[d].pattern) {
      names.insert(AnyDeclID(program[n].decl))
      cache.declsUnderChecking.insert(AnyDeclID(program[n].decl))
    }

    defer {
      cache.declsUnderChecking.remove(AnyDeclID(d))
      cache.declsUnderChecking.subtract(names)
      assert(names.allSatisfy({ cache.local.declType[$0] != nil }))
    }

    var obligations = ProofObligations(scope: program[d].scope)
    let t = inferredType(of: d, usedAs: purpose, updating: &obligations)
    let s = discharge(obligations, relatedTo: d)
    let u = s.substitutions.reify(t)
    cache.write(s.isSound ? u : .error, at: \.declType[d], ignoringSharedCache: ignoreSharedCache)
    return u
  }

  /// Type checks `e` and returns its type, using `hint` as contextual type information.
  private mutating func checkedType(of e: AnyExprID, withHint hint: AnyType? = nil) -> AnyType {
    let (incompleteType, obligations) = partiallyCheckedType(of: e, withHint: hint)
    let s = discharge(obligations, relatedTo: e)
    return s.substitutions.reify(incompleteType)
  }

  /// Type checks `e` as an argument to `p` and returns its type.
  private mutating func checkedType(
    of e: AnyExprID, asArgumentTo p: ParameterType
  ) -> AnyType {
    var (incompleteType, obligations) = partiallyCheckedType(of: e, withHint: p.bareType)
    obligations.insert(
      ParameterConstraint(incompleteType, ^p, origin: .init(.argument, at: program[e].site)))
    let s = discharge(obligations, relatedTo: e)
    return s.substitutions.reify(incompleteType)
  }

  /// Returns the inferred type of `e`, along with a set of goals to solve to check that type.
  private mutating func partiallyCheckedType(
    of e: AnyExprID, withHint hint: AnyType? = nil
  ) -> (AnyType, ProofObligations) {
    var obligations = ProofObligations(scope: program[e].scope)
    let t = inferredType(of: e, withHint: hint, updating: &obligations)
    return (t, obligations)
  }

  /// Calls `action` with the innermost generic scopes containing `s`.
  ///
  /// A scope `s` inherits from a generic environment `g` if:
  /// - `s` is notionally contained in `g`; and/or
  /// - `s` is an extension and `g` is the environment of the type extended by `s`.
  private mutating func forEachGenericParentScope(
    inheritedBy s: AnyScopeID,
    do action: (inout Self, AnyScopeID) -> Void
  ) {
    switch s.kind {
    case ModuleDecl.self:
      return
    case ConformanceDecl.self:
      if let e = scopeExtended(by: ConformanceDecl.ID(s)!) { action(&self, e) }
    case ExtensionDecl.self:
      if let e = scopeExtended(by: ExtensionDecl.ID(s)!) { action(&self, e) }
    default:
      break
    }

    if let s = program.scopes(from: program[s].scope).first(where: \.isGenericScope) {
      action(&self, s)
    }
  }

  /// Returns the generic environment introduced by `s`, if any.
  private mutating func environment(of s: AnyScopeID) -> GenericEnvironment? {
    switch s.kind {
    case ConformanceDecl.self:
      return environment(of: ConformanceDecl.ID(s)!)
    case ExtensionDecl.self:
      return environment(of: ExtensionDecl.ID(s)!)
    case FunctionDecl.self:
      return environment(of: FunctionDecl.ID(s)!)
    case InitializerDecl.self:
      return environment(of: InitializerDecl.ID(s)!)
    case MethodDecl.self:
      return environment(of: MethodDecl.ID(s)!)
    case ProductTypeDecl.self:
      return environment(of: ProductTypeDecl.ID(s)!)
    case SubscriptDecl.self:
      return environment(of: SubscriptDecl.ID(s)!)
    case TypeAliasDecl.self:
      return environment(of: TypeAliasDecl.ID(s)!)
    case TraitDecl.self:
      return environment(of: TraitDecl.ID(s)!)
    default:
      return nil
    }
  }

  /// Returns the generic environment introduced by `d`.
  private mutating func environment<T: GenericDecl & LexicalScope>(
    of d: T.ID
  ) -> GenericEnvironment {
    if let e = cache.read(\.environment[d]) { return e }

    guard let clause = program[d].genericClause?.value else {
      let e = initialEnvironment(of: d, introducing: [])
      return commit(e)
    }

    var partialResult = initialEnvironment(of: d, introducing: clause.parameters)

    for p in clause.parameters {
      let lhs = uncheckedType(of: p)

      // Nothing more to do if the parameter isn't type-kinded or doesn't have trait bounds.
      let bounds = program[p].conformances
      guard !bounds.isEmpty, let t = MetatypeType(lhs) else { continue }

      for (n, u) in evalTraitComposition(bounds) {
        partialResult.registerConstraint(.init(.conformance(t.instance, u), at: program[n].site))
        insertConformanceRequirement(t.instance, u, in: &partialResult)
        cache.partiallyFormedEnvironment[d] = partialResult
      }
    }

    if let w = clause.whereClause {
      for c in w.value.constraints {
        insertConstraint(c, in: &partialResult)
      }
    }

    return commit(partialResult)
  }

  /// Returns the generic environment introduced by `d`.
  private mutating func environment(of d: TraitDecl.ID) -> GenericEnvironment {
    // Environment already created?
    if let e = cache.read(\.environment[d]) { return e }
    let t = TraitType(uncheckedType(of: d))!

    // Create a partially formed environment to break cycles in general name resolution.
    var partialResult = GenericEnvironment(of: AnyDeclID(d), introducing: [program[d].receiver.id])
    cache.partiallyFormedEnvironment[d] = partialResult

    // Recursive constraints involving more than a single trait are not supported yet.
    let c = traitComponent(containing: t)
    if cache.traitDependencyComponents.vertices(in: c).count > 1 {
      report(.error(circularRefinementAt: program[d].introducerSite))
      return commit(partialResult)
    }

    // Gather the requirements defined by trait dependencies, ignoring those on generic parameters
    // not introduced nor captured by the environment.
    partialResult.registerDependencies(dependencies(of: d))
    for u in partialResult.dependencies where u != t {
      for r in environment(of: u.decl).publicRules {
        if !r.parametersAreContained(in: partialResult.parameters) { continue }
        insertRequirement(r, in: &partialResult)
      }
    }

    // Requirements gathered so far are not inherited by dependent environments.
    partialResult.markRequirementsAsInherited()

    generatePublicRequirements(of: t, in: &partialResult)
    return commit(partialResult)
  }

  /// Inserts the public requirements introduced by the generic signature of `t` in its partially
  /// formed environment.
  private mutating func generatePublicRequirements(
    of t: TraitType,
    in partiallyFormedEnvironment: inout GenericEnvironment
  ) {
    // Synthesize `Self: T`.
    let s = GenericTypeParameterType(selfParameterOf: t.decl, in: program.ast)
    partiallyFormedEnvironment.registerConstraint(
      .init(.conformance(^s, t), at: program[t.decl].identifier.site))
    insertRequirement(
      RequirementRule([.trait(t.decl), .trait(t.decl)], [.trait(t.decl)]),
      in: &partiallyFormedEnvironment)
    insertRequirement(
      RequirementRule([.parameterType(s.decl), .trait(t.decl)], [.parameterType(s.decl)]),
      in: &partiallyFormedEnvironment)

    // Traits are never nested in generic scopes. Their dependencies and parameters are defined by
    // the traits that they refine.
    for u in bases(of: t).unordered where u != t {
      let e = environment(of: u.decl)
      partiallyFormedEnvironment.registerConstraints(e.constraints)
      let v = RequirementTerm([.parameterType(program[u.decl].receiver.id)])
      for r in e.publicRules {
        insertRequirement(
          r.substituting(v, for: [.parameterType(s.decl)]),
          in: &partiallyFormedEnvironment)
      }
    }

    // Name resolution can use `Self: T` and its consequences to form additional constraints.
    cache.partiallyFormedEnvironment[t.decl] = partiallyFormedEnvironment

    for m in program[t.decl].members {
      switch m.kind {
      case AssociatedTypeDecl.self:
        insertConstraints(of: AssociatedTypeDecl.ID(m)!, in: &partiallyFormedEnvironment)
      case AssociatedValueDecl.self:
        insertConstraints(of: AssociatedValueDecl.ID(m)!, in: &partiallyFormedEnvironment)
      default:
        continue
      }
    }
  }

  /// Returns the generic environment introduced by `d`.
  private mutating func environment<T: TypeExtendingDecl>(of d: T.ID) -> GenericEnvironment {
    if let e = cache.read(\.environment[d]) { return e }

    var partialResult = initialEnvironment(of: d, introducing: [])
    for c in (program[d].whereClause?.value.constraints ?? []) {
      insertConstraint(c, in: &partialResult)
    }

    return commit(partialResult)
  }

  /// Creates the partially formed generic environment of `d`, which introduces `parameters`,
  /// initialized with constraints inherited from the enclosing generic environment.
  private mutating func initialEnvironment<T: Decl>(
    of d: T.ID, introducing parameters: [GenericParameterDecl.ID]
  ) -> GenericEnvironment {
    if let e = cache.partiallyFormedEnvironment[d] {
      return e
    }

    // Create a partially formed environment to break cycles in general name resolution.
    var e = GenericEnvironment(of: AnyDeclID(d), introducing: parameters)
    cache.partiallyFormedEnvironment[d] = e
    e.registerDependencies(dependencies(of: d))
    e.markRequirementsAsInherited()

    // Gather the parameters and requirements defined by generic parent scopes.
    forEachGenericParentScope(inheritedBy: AnyScopeID(d)!) { (me, p) in
      let inheritedEnvironment = me.environment(of: p)!
      e.registerInheritance(inheritedEnvironment)
      for r in inheritedEnvironment.publicRules {
        me.insertRequirement(r, in: &e)
      }
    }

    // Gather the requirements defined by trait dependencies, ignoring those on generic parameters
    // not introduced nor captured by the environment.
    for u in e.dependencies where u.decl.rawValue != d.rawValue {
      for r in environment(of: u.decl).publicRules {
        if !r.parametersAreContained(in: e.parameters) { continue }
        insertRequirement(r, in: &e)
      }
    }

    cache.partiallyFormedEnvironment[d] = e
    return e
  }

  /// Returns the generic environment introduced by `d`, which may be partially formed.
  private mutating func possiblyPartiallyFormedEnvironment(
    of d: AnyDeclID
  ) -> GenericEnvironment? {
    if let e = cache.partiallyFormedEnvironment[d] {
      return e
    } else if let s = AnyScopeID(d) {
      return environment(of: s)
    } else {
      return nil
    }
  }

  /// Writes `finalResult` to the cache.
  private mutating func commit(_ finalResult: consuming GenericEnvironment) -> GenericEnvironment {
    var e = finalResult
    if !e.requirements.complete(orderingTermsWith: { (a, b) in compareOrder(a, b) }) {
      report(.error(cannotConstructRequirementSystem: e.decl, in: program.ast))
    }

    cache.partiallyFormedEnvironment[e.decl] = nil
    cache.write(e, at: \.environment[e.decl])
    return e
  }

  /// Inserts `d`'s constraints in `e`.
  ///
  /// `e` is the environment in which `d` is introduced.
  private mutating func insertConstraints(
    of d: AssociatedTypeDecl.ID, in e: inout GenericEnvironment
  ) {
    // Synthesize sugared conformance constraint, if any.
    if let lhs = MetatypeType(uncheckedType(of: d))?.instance {
      for (n, t) in evalTraitComposition(program[d].conformances) {
        e.registerConstraint(.init(.conformance(lhs, t), at: program[n].site))
        insertConformanceRequirement(lhs, t, in: &e)
        cache.partiallyFormedEnvironment[e.decl] = e
      }
    }

    for c in (program[d].whereClause?.value.constraints ?? []) {
      insertConstraint(c, in: &e)
    }
  }

  /// Inserts `d`'s constraints in `e`.
  ///
  /// `e` is the environment in which `d` is introduced.
  private mutating func insertConstraints(
    of d: AssociatedValueDecl.ID, in e: inout GenericEnvironment
  ) {
    for c in (program[d].whereClause?.value.constraints ?? []) {
      insertConstraint(c, in: &e)
    }
  }

  /// Evaluates `c` as a generic constraint and inserts it in `e`.
  private mutating func insertConstraint(
    _ c: SourceRepresentable<WhereClause.ConstraintExpr>, in e: inout GenericEnvironment
  ) {
    switch c.value {
    case .equality(let l, let r):
      guard
        let lhs = evalTypeAnnotation(AnyExprID(l)).errorFree,
        let rhs = evalTypeAnnotation(r).errorFree
      else { return }

      if lhs.isTypeParameter || rhs.isTypeParameter {
        e.registerConstraint(.init(.equality(lhs, rhs), at: c.site))
        insertEqualityRequirement(lhs, rhs, in: &e)
        cache.partiallyFormedEnvironment[e.decl] = e
      } else {
        report(.error(invalidEqualityConstraintBetween: lhs, and: rhs, at: c.site))
      }

    case .bound(let l, let r):
      guard let lhs = evalTypeAnnotation(AnyExprID(l)).errorFree else { return }
      guard lhs.isTypeParameter else {
        report(.error(invalidConformanceConstraintTo: lhs, at: c.site))
        return
      }

      for (_, rhs) in evalTraitComposition(r) {
        e.registerConstraint(.init(.conformance(lhs, rhs), at: c.site))
        insertConformanceRequirement(lhs, rhs, in: &e)
        cache.partiallyFormedEnvironment[e.decl] = e
      }

    case .value:
      UNIMPLEMENTED("generic value constraints")
    }
  }

  /// Inserts a rule in `e`'s requirement system specifying that `l` conforms to `r`.
  private mutating func insertConformanceRequirement(
    _ l: AnyType, _ r: TraitType, in e: inout GenericEnvironment
  ) {
    let f = possiblyPartiallyFormedEnvironment(of: AnyDeclID(r.decl))!
    let u = RequirementTerm([.parameterType(program[r.decl].receiver.id)])
    var v = buildTerm(l)

    if let t = TraitDecl.ID(e.decl), l.base is AssociatedTypeType {
      assert(v.first == .parameterType(program[t].receiver))
      v = .init(v.dropFirst())
    }

    for rule in f.publicRules {
      insertRequirement(rule.substituting(u, for: v), in: &e)
    }
  }

  /// Inserts a rule in `e`'s requirement system specifying that `l` is equal to `r`.
  private mutating func insertEqualityRequirement(
    _ l: AnyType, _ r: AnyType, in e: inout GenericEnvironment
  ) {
    // Make sure `a` is not concrete.
    let (a, b) = l.isTypeParameter ? (l, r) : (r, l)
    assert(a.isTypeParameter)

    // Rule orientation depends on ordering.
    var v = buildTerm(a)
    var u = buildTerm(b)

    if let t = TraitDecl.ID(e.decl) {
      v = v.substituting([.parameterType(program[t].receiver)], for: [.trait(t)])
      u = u.substituting([.parameterType(program[t].receiver)], for: [.trait(t)])
    }

    if compareOrder(u, v) == .ascending { swap(&v, &u) }
    insertRequirement(.init(u, v), in: &e)
  }

  /// Inserts the requirement `r` into `e`.
  @discardableResult
  private mutating func insertRequirement(
    _ r: RequirementRule, in e: inout GenericEnvironment
  ) -> (inserted: Bool, ruleAfterInsertion: RequirementSystem.RuleID) {
    e.requirements.insert(r, orderingTermsWith: { (a, b) in compareOrder(a, b) })
  }

  /// Returns the traits to which a conformance can be derived in the environment of `d`.
  private mutating func dependencies<T: Decl>(of d: T.ID) -> [TraitType] {
    var work = traitMentions(in: d)
    var seen: [TraitType] = []

    while let u = work.popLast() {
      if !seen.contains(u) {
        work.append(contentsOf: traitMentions(in: u.decl))
        seen.append(u)
      }
    }

    return seen
  }

  /// Returns the traits to which a conformance can be derived given the constraints in `d`.
  private mutating func traitMentions<T: Decl>(in d: T.ID) -> [TraitType] {
    switch d.kind {
    case ConformanceDecl.self:
      return traitMentions(in: ConformanceDecl.ID(d)!)
    case ExtensionDecl.self:
      return traitMentions(in: ExtensionDecl.ID(d)!)
    case TraitDecl.self:
      return traitMentions(in: TraitDecl.ID(d)!)
    default:
      if let g = (program.ast[d] as? GenericDecl)?.genericClause?.value {
        return traitMentions(in: g)
      } else {
        return []
      }
    }
  }

  /// Returns the traits to which a conformance can be derived given the constraints in `d`.
  private mutating func traitMentions(in d: ConformanceDecl.ID) -> [TraitType] {
    var result = evalTraitComposition(program[d].conformances).map(\.trait)
    if let w = program[d].whereClause {
      result.append(contentsOf: traitMentions(in: w.value))
    }
    return result
  }

  /// Returns the traits to which a conformance can be derived given the constraints in `d`.
  private mutating func traitMentions(in d: ExtensionDecl.ID) -> [TraitType] {
    if let w = program[d].whereClause {
      return traitMentions(in: w.value)
    } else {
      return []
    }
  }

  /// Returns the traits to which a conformance can be derived given the constraints in `d`.
  private mutating func traitMentions(in d: TraitDecl.ID) -> [TraitType] {
    if let s = cache.traitToSuccessors[d] { return s }

    // Enumerate base traits.
    var result = evalTraitComposition(program[d].bounds).map(\.trait)

    // Enumerate traits occurring in associated type declarations.
    for m in program[d].members.filter(AssociatedTypeDecl.self) {
      result.append(contentsOf: evalTraitComposition(program[m].conformances).map(\.trait))
      if let w = program[m].whereClause {
        result.append(contentsOf: traitMentions(in: w.value))
      }
    }

    cache.traitToSuccessors[d] = result
    return result
  }

  /// Returns the traits to which a conformance can be derived given the constraints in `g`.
  private mutating func traitMentions(in g: GenericClause) -> [TraitType] {
    var result: [TraitType] = []
    for m in g.parameters where uncheckedType(of: m).base is MetatypeType {
      result.append(contentsOf: evalTraitComposition(program[m].conformances).map(\.trait))
    }
    if let w = g.whereClause {
      result.append(contentsOf: traitMentions(in: w.value))
    }
    return result
  }

  /// Returns the traits to which a conformance can be derived given the constraints in `w`.
  private mutating func traitMentions(in w: WhereClause) -> [TraitType] {
    var result: [TraitType] = []
    for c in w.constraints {
      if case .bound(_, let r) = c.value {
        for n in r {
          if let u = TraitType(evalTypeAnnotation(AnyExprID(n))) { result.append(u) }
        }
      }
    }
    return result
  }

  /// Returns the strongly connected component that contains `t` in the trait dependency graph.
  private mutating func traitComponent(containing t: TraitType) -> Int {
    var s = StronglyConnectedComponents<TraitType>()
    swap(&cache.traitDependencyComponents, &s)
    let i = s.component(
      containing: t,
      enumeratingSuccessorsWith: { (v) in traitMentions(in: v.decl) })
    swap(&cache.traitDependencyComponents, &s)
    return i
  }

  /// Returns the type of `d`, computing it if necessary, without type checking `d`.
  ///
  /// This method returns the value for `d` in `cache[\.declType]` or `cache.uncheckedType` if
  /// it has been computed. Otherwise, it calls `_uncheckedType(d)` with `cache.uncheckedType[d]`
  /// assigned to `.inProgress`. After the call, `cache.uncheckedType[d] == .complete(t)`, where
  /// `t` is the return value. A diagnostic is reported if type the type of `d` contains an error.
  ///
  /// - Requires: `cache.uncheckedType[d] != .inProgress`
  private mutating func uncheckedType<T: DeclID>(
    of d: T, ignoringSharedCache ignoreSharedCache: Bool = false
  ) -> AnyType {
    // Check for infinite recursion.
    if let t = cache.uncheckedType[d] {
      if let u = t.computed {
        return u
      } else {
        report(.error(recursiveDefinition: AnyDeclID(d), in: program.ast))
        return .error
      }
    } else {
      cache.uncheckedType[d] = .inProgress
    }

    // Check if work has to be done.
    if let t = cache.read(\.declType[d], ignoringSharedCache: ignoreSharedCache) {
      return commitUncheckedType(t, for: AnyDeclID(d))
    }

    // Do the work.
    var result: AnyType
    switch d.kind {
    case AssociatedTypeDecl.self:
      result = _uncheckedType(of: AssociatedTypeDecl.ID(d)!)
    case AssociatedValueDecl.self:
      result = _uncheckedType(of: AssociatedValueDecl.ID(d)!)
    case BindingDecl.self:
      result = _uncheckedType(of: BindingDecl.ID(d)!)
    case ConformanceDecl.self:
      result = _uncheckedType(of: ConformanceDecl.ID(d)!)
    case ExtensionDecl.self:
      result = _uncheckedType(of: ExtensionDecl.ID(d)!)
    case FunctionDecl.self:
      result = _uncheckedType(of: FunctionDecl.ID(d)!)
    case GenericParameterDecl.self:
      result = _uncheckedType(of: GenericParameterDecl.ID(d)!)
    case ImportDecl.self:
      result = _uncheckedType(of: ImportDecl.ID(d)!)
    case InitializerDecl.self:
      result = _uncheckedType(of: InitializerDecl.ID(d)!)
    case MethodDecl.self:
      result = _uncheckedType(of: MethodDecl.ID(d)!)
    case MethodImpl.self:
      result = _uncheckedType(of: MethodImpl.ID(d)!)
    case ModuleDecl.self:
      result = _uncheckedType(of: ModuleDecl.ID(d)!)
    case NamespaceDecl.self:
      result = _uncheckedType(of: NamespaceDecl.ID(d)!)
    case OperatorDecl.self:
      result = _uncheckedType(of: OperatorDecl.ID(d)!)
    case ParameterDecl.self:
      result = _uncheckedType(of: ParameterDecl.ID(d)!)
    case ProductTypeDecl.self:
      result = _uncheckedType(of: ProductTypeDecl.ID(d)!)
    case SubscriptDecl.self:
      result = _uncheckedType(of: SubscriptDecl.ID(d)!)
    case SubscriptImpl.self:
      result = _uncheckedType(of: SubscriptImpl.ID(d)!)
    case TraitDecl.self:
      result = _uncheckedType(of: TraitDecl.ID(d)!)
    case TypeAliasDecl.self:
      result = _uncheckedType(of: TypeAliasDecl.ID(d)!)
    case VarDecl.self:
      result = _uncheckedType(of: VarDecl.ID(d)!)
    default:
      unexpected(d, in: program.ast)
    }

    return commitUncheckedType(result, for: AnyDeclID(d))
  }

  /// Commits `t` as the unchecked type of `d` to the local cache.
  private mutating func commitUncheckedType(_ t: AnyType, for d: AnyDeclID) -> AnyType {
    modify(&cache.uncheckedType[d]!) { (old) in
      if let u = old.computed { assert(u == t, "non-monotonic update") }
      old = .computed(t)
    }
    return t
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: AssociatedTypeDecl.ID) -> AnyType {
    // Parent scope must be a trait declaration.
    let traitDecl = TraitDecl.ID(program[d].scope)!
    let instance = AssociatedTypeType(
      NodeID(d)!,
      domain: ^GenericTypeParameterType(selfParameterOf: traitDecl, in: program.ast),
      ast: program.ast)
    return ^MetatypeType(of: instance)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: AssociatedValueDecl.ID) -> AnyType {
    // Parent scope must be a trait declaration.
    let traitDecl = TraitDecl.ID(program[d].scope)!
    let instance = AssociatedValueType(
      NodeID(d)!,
      domain: ^GenericTypeParameterType(selfParameterOf: traitDecl, in: program.ast),
      ast: program.ast)
    return ^MetatypeType(of: instance)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: BindingDecl.ID) -> AnyType {
    checkedType(of: d)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType<T: TypeExtendingDecl>(of d: T.ID) -> AnyType {
    let (i, cs) = eval(existentialBound: program[d].subject)
    guard cs.isEmpty else { UNIMPLEMENTED() }

    switch i.base {
    case is BuiltinType, is RemoteType:
      report(.error(cannotExtend: i, at: program[d].subject.site))
    case let t as TraitType:
      return ^GenericTypeParameterType(selfParameterOf: t.decl, in: program.ast)
    default:
      return i
    }

    return .error
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: FunctionDecl.ID) -> AnyType {
    let inputs = uncheckedInputTypes(of: program[d].parameters, declaredBy: d)
    let output = evalReturnTypeAnnotation(of: d)

    if program.isNonStaticMember(d) {
      let k = program[d].receiverEffect?.value ?? .let
      let r = resolveReceiverMetatype(in: program[d].scope)!.instance
      cache.write(^ParameterType(k, r), at: \.declType[program[d].receiver!])

      let e = TupleType([.init(label: "self", type: k == .sink ? r : ^RemoteType(k, r))])
      return ^ArrowType(receiverEffect: k, environment: ^e, inputs: inputs, output: output)
    }

    assert(program[d].receiver == nil)
    let captures = uncheckedCaptureTypes(of: d)
    let e = TupleType(captures.explicit + captures.implicit)
    return ^ArrowType(environment: ^e, inputs: inputs, output: output)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: GenericParameterDecl.ID) -> AnyType {
    if program[d].isTypeKinded {
      return ^MetatypeType(of: GenericTypeParameterType(d, ast: program.ast))
    } else {
      let bound = program[d].conformances.uniqueElement!
      return evalTypeAnnotation(AnyExprID(bound))
    }
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: ImportDecl.ID) -> AnyType {
    guard let m = program.ast.module(named: program[d].baseName) else {
      report(.error(noSuchModule: program[d].baseName, at: program[d].identifier.site))
      return .error
    }
    return ^ModuleType(m, ast: program.ast)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: InitializerDecl.ID) -> AnyType {
    if program[d].isMemberwise {
      let productTypeDecl = ProductTypeDecl.ID(program[d].scope)!
      let t = memberwiseInitializer(of: productTypeDecl)
      cache.write(t.inputs[0].type, at: \.declType[program[d].receiver])
      return ^t
    }

    let r = resolveReceiverMetatype(in: program[d].scope)!.instance
    let t = ^ParameterType(.set, r)
    cache.write(t, at: \.declType[program[d].receiver])

    let i = CallableTypeParameter(label: "self", type: t)
    let inputs = uncheckedInputTypes(of: program[d].parameters, declaredBy: d)
    return ^ArrowType(environment: .void, inputs: [i] + inputs, output: .void)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: MethodDecl.ID) -> AnyType {
    let inputs = uncheckedInputTypes(of: program[d].parameters, declaredBy: d)
    let output = evalReturnTypeAnnotation(of: d)

    let r = resolveReceiverMetatype(in: program[d].scope)!.instance
    return ^MethodType(
      capabilities: .init(program[d].impls.map({ program[$0].introducer.value })),
      receiver: r,
      inputs: inputs,
      output: output)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: MethodImpl.ID) -> AnyType {
    guard let bundle = MethodType(uncheckedType(of: AnyDeclID(program[d].scope)!)) else {
      return .error
    }

    let k = program[d].introducer.value
    cache.write(^ParameterType(k, bundle.receiver), at: \.declType[program[d].receiver])
    return ^bundle.variant(k)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: ModuleDecl.ID) -> AnyType {
    ^ModuleType(d, ast: program.ast)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: OperatorDecl.ID) -> AnyType {
    .void
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: NamespaceDecl.ID) -> AnyType {
    ^NamespaceType(d, ast: program.ast)
  }

  /// Computes and returns the type of `d`.
  ///
  /// - Requires: `d` has a type annotation.
  private mutating func _uncheckedType(of d: ParameterDecl.ID) -> AnyType {
    let a = program[d].annotation ?? preconditionFailure("missing type annotation")
    let t = evalParameterAnnotation(a)

    // The annotation may not omit generic arguments.
    if t[.hasVariable] {
      report(.error(notEnoughContextToInferArgumentsAt: program[a].site))
      return t.replacingVariablesWithErrors
    }

    return t
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: ProductTypeDecl.ID) -> AnyType {
    ^MetatypeType(of: ProductType(d, ast: program.ast))
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: SubscriptDecl.ID) -> AnyType {
    let inputs = uncheckedInputTypes(of: program[d].parameters, declaredBy: d)
    let output = evalTypeAnnotation(program[d].output)

    let e: TupleType
    if program.isNonStaticMember(d) {
      let r = resolveReceiverMetatype(in: program[d].scope)!.instance
      e = TupleType([.init(label: "self", type: ^RemoteType(.yielded, r))])
    } else {
      let captures = uncheckedCaptureTypes(of: d)
      e = TupleType(captures.explicit + captures.implicit)
    }

    return ^SubscriptType(
      isProperty: program[d].isProperty,
      capabilities: .init(program[d].impls.map({ program[$0].introducer.value })),
      environment: ^e,
      inputs: inputs,
      output: output)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: SubscriptImpl.ID) -> AnyType {
    guard let bundle = SubscriptType(uncheckedType(of: AnyDeclID(program[d].scope)!)) else {
      return .error
    }

    let k = program[d].introducer.value
    assert(bundle.capabilities.contains(k))

    let t = bundle.transformParts { (t) in
      switch t.base {
      case let u as ParameterType where u.access == .yielded:
        return .stepInto(^ParameterType(k, u.bareType))
      case let u as RemoteType where u.access == .yielded:
        return .stepInto(^RemoteType(k, u.bareType))
      default:
        return .stepInto(t)
      }
    }

    if let s = program[d].receiver {
      let r = RemoteType(t.captures[0].type)!
      cache.write(^ParameterType(r), at: \.declType[s])
    }

    return ^SubscriptImplType(
      isProperty: t.isProperty,
      receiverEffect: k,
      environment: t.environment,
      inputs: t.inputs,
      output: t.output)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: TraitDecl.ID) -> AnyType {
    ^TraitType(d, ast: program.ast)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: TypeAliasDecl.ID) -> AnyType {
    let t = evalTypeAnnotation(program[d].aliasedType)
    let a = TypeAliasType(aliasing: t, declaredBy: d, in: program.ast)
    return ^MetatypeType(of: a)
  }

  /// Computes and returns the type of `d`.
  private mutating func _uncheckedType(of d: VarDecl.ID) -> AnyType {
    check(program[d].binding, ignoringSharedCache: true)
    return cache.local.declType[d]!
  }

  /// Computes and returns the types of `d`'s captures.
  ///
  /// - Requires: `d` is not a member declaration.
  private mutating func uncheckedCaptureTypes<T: CapturingDecl>(
    of d: T.ID
  ) -> (explicit: [TupleType.Element], implicit: [TupleType.Element]) {
    let e = explicitCaptures(program[d].explicitCaptures, of: d)
    let i = implicitCaptures(of: d, ignoring: Set(e.map(\.label!)))
    return (e, i)
  }

  /// Computes and returns the types of the inputs `ps` of `d`.
  ///
  /// - Requires: The parameters in `ps` have type annotations.
  private mutating func uncheckedInputTypes<T: Decl & LexicalScope>(
    of ps: [ParameterDecl.ID], declaredBy d: T.ID
  ) -> [CallableTypeParameter] {
    // The generic environment of the declaration is built before we can resolve the types of the
    // parameter annotations to avoid infinite recursion in cases the bounds of a generic parameter
    // lead name resolution back to environment (e.g., `<T: P>(x: T)` in a trait extension.)
    _ = environment(of: AnyScopeID(d))

    var result: [CallableTypeParameter] = []
    for p in ps {
      precondition(program[p].annotation != nil)
      let i = CallableTypeParameter(
        label: program[p].label?.value,
        type: uncheckedType(of: p, ignoringSharedCache: true),
        hasDefault: program[p].defaultValue != nil,
        isImplicit: program[p].isImplicit)
      result.append(i)
    }
    return result
  }

  /// Computes and returns the types of the inputs of `e`'s underlying declaration, using `hint`
  /// to guess the passing conventions of unanotated parameters.
  ///
  /// `hint` is used as contextual information to refine guesses iff it is a lambda type with the
  /// same number of parameters as `e`. Parameter annotations take precedence in case of conflict.
  ///
  /// After the call, `cache.uncheckedType[p]` may be assigned to a type variable if `p` has no
  /// type annotation. Type checking is expected to reify such variables once the type of the
  /// expression in which `e` occurs has been checked.
  private mutating func uncheckedInputTypes(
    of e: LambdaExpr.ID, withHint hint: ArrowType?
  ) -> [CallableTypeParameter] {
    let d = program[e].decl.id
    let ps = program[d].parameters

    // Fast path: all parameters have an annotation.
    if ps.allSatisfy({ program[$0].annotation != nil }) {
      return uncheckedInputTypes(of: ps, declaredBy: d)
    }

    // Slow path: infer elided conventions from the uses in the lambda's body.
    let inputHints = hint.flatMap({ $0.inputs.count == ps.count ? $0.inputs : nil })
    let inferredConventions = uncheckedPassingConventions(of: e, withHint: inputHints)
    var result: [CallableTypeParameter] = []

    for (i, p) in ps.enumerated() {
      let t: AnyType
      if program[p].annotation != nil {
        t = uncheckedType(of: p, ignoringSharedCache: true)
      } else if let u = cache.uncheckedType[p]?.computed {
        t = u
      } else {
        t = inputHints?[i].type ?? ^ParameterType(inferredConventions[i], ^freshVariable())
        cache.uncheckedType[p] = .computed(t)
      }
      result.append(.init(label: program[p].label?.value, type: t))
    }
    return result
  }

  /// Returns the passing conventions of `e`'s parameters inferred from uses in `e`'s body.
  ///
  /// Parameters used immutably are inferred to be passed `let` unless corresponding hints specify
  /// a different convention. Parameters used mutably are inferred to be passed `inout` unless
  /// corresponding hints specify a convention other than `let`.
  ///
  /// - Requires: `hint` is `nil` or contains has as many elements as `e`'s parameters.
  private mutating func uncheckedPassingConventions(
    of e: LambdaExpr.ID, withHint hint: [CallableTypeParameter]?
  ) -> [AccessEffect] {
    let ps = program[e].decl.parameters
    var result: [AccessEffect]
    if let h = hint {
      result = h.map({ ParameterType($0.type)?.access ?? .let })
    } else {
      result = .init(repeating: .let, count: ps.count)
    }

    // Look at uses to update conventions where we could only guess `let` from the context.
    for (n, m) in program.ast.uses(in: program[e].decl) {
      let candidates = lookup(unqualified: program[n].name.value.stem, in: program[n].scope)
      if let i = candidates.unique(ParameterDecl.self).flatMap(ps.firstIndex(of:)) {
        if result[i] == .let {
          result[i] = m
        }
      }
    }

    return result
  }

  /// Computes and returns the type of values expected to be returned or projected in `scopeOfUse`,
  /// or returns `nil` if `scopeOfUse` is not nested in the declaration of a callable entity.
  private mutating func uncheckedOutputType(in scopeOfUse: AnyScopeID) -> AnyType? {
    switch scopeOfUse.kind {
    case ModuleDecl.self:
      return nil
    case FunctionDecl.self:
      return uncheckedOutputType(of: FunctionDecl.ID(scopeOfUse)!)
    case InitializerDecl.self:
      return .void
    case MethodImpl.self:
      return uncheckedOutputType(of: MethodImpl.ID(scopeOfUse)!)
    case SubscriptImpl.self:
      return uncheckedOutputType(of: SubscriptImpl.ID(scopeOfUse)!)
    default:
      return uncheckedOutputType(in: program[scopeOfUse].scope)
    }
  }

  /// Computes and returns the type of values returned by `d`.
  private mutating func uncheckedOutputType(of d: FunctionDecl.ID) -> AnyType {
    ArrowType(uncheckedType(of: d))?.output ?? .error
  }

  /// Computes and returns the type of values returned by `d`.
  private mutating func uncheckedOutputType(of d: MethodImpl.ID) -> AnyType {
    ArrowType(uncheckedType(of: d))?.output ?? .error
  }

  /// Computes and returns the type of values projected by `d`.
  private mutating func uncheckedOutputType(of d: SubscriptImpl.ID) -> AnyType {
    SubscriptImplType(uncheckedType(of: d))?.output ?? .error
  }

  /// Returns the types of the explicit captures `cs` of `d`.
  private mutating func explicitCaptures<T: Decl & LexicalScope>(
    _ cs: [BindingDecl.ID], of d: T.ID
  ) -> [TupleType.Element] {
    var result: [TupleType.Element] = []
    var sibligns = Set<String>()

    for c in cs {
      let t = uncheckedType(of: c, ignoringSharedCache: true)
      for (_, n) in program.ast.names(in: program[c].pattern) {
        if !sibligns.insert(program[n].decl.baseName).inserted {
          report(.error(duplicateCaptureNamed: program[n].decl.baseName, at: program[n].site))
          continue
        }

        let label = program[n].decl.identifier.value
        switch program[c].pattern.introducer.value {
        case .let:
          result.append(.init(label: label, type: ^RemoteType(.let, t)))
        case .inout:
          result.append(.init(label: label, type: ^RemoteType(.inout, t)))
        case .sinklet, .var:
          result.append(.init(label: label, type: ^t))
        }
      }
    }

    return result
  }

  /// Returns the implicit captures found in the body of `d`.
  private mutating func implicitCaptures<T: CapturingDecl>(
    of d: T.ID, ignoring explicitCaptures: Set<String>
  ) -> [TupleType.Element] {
    // Only local declarations have captures.
    if !program.isLocal(d) {
      cache.write([], at: \.implicitCaptures[d])
      return []
    }

    var captureToStemAndEffect: [AnyDeclID: (stem: String, effect: AccessEffect)] = [:]
    for (name, mutability) in program.ast.uses(in: d) {
      guard
        let (stem, pick) = lookupImplicitCapture(name, occurringIn: d),
        !explicitCaptures.contains(stem)
      else { continue }

      modify(&captureToStemAndEffect[pick, default: (stem, .let)]) { (x) in
        x.effect = max(x.effect, mutability)
      }
    }

    var captures: [ImplicitCapture] = []
    var types: [TupleType.Element] = []
    for (c, x) in captureToStemAndEffect {
      let t = resolveType(of: c, exposedTo: AnyScopeID(d), reportingDiagnosticsAt: program[d].site)
      if t[.hasError] { continue }

      let u = RemoteType(x.effect, t)
      captures.append(ImplicitCapture(name: .init(stem: x.stem), type: u, decl: c))
      types.append(.init(label: x.stem, type: ^u))
    }

    cache.write(captures, at: \.implicitCaptures[d])
    return types
  }

  /// Returns type of `d`'s memberwise initializer.
  private mutating func memberwiseInitializer(of d: ProductTypeDecl.ID) -> ArrowType {
    let r = resolveReceiverMetatype(in: d)!.instance
    var inputs = [CallableTypeParameter(label: "self", type: ^ParameterType(.set, r))]

    for m in program[d].members.filter(BindingDecl.self) {
      check(m)
      for (_, n) in program.ast.names(in: program[m].pattern) {
        let d = program[n].decl.id
        let t = ParameterType(.sink, cache[\.declType[d]]!)
        inputs.append(.init(label: program[d].baseName, type: ^t))
      }
    }

    return ArrowType(environment: .void, inputs: inputs, output: .void)
  }

  /// Returns the model for which `d` declares conformances.
  ///
  /// - Requires: `d` is a conformance source.
  private mutating func extendedModel(_ d: AnyDeclID) -> AnyType {
    switch d.kind {
    case ProductTypeDecl.self:
      return resolveReceiverMetatype(in: ProductTypeDecl.ID(d)!)!.instance
    case ConformanceDecl.self:
      return resolveReceiverMetatype(in: ConformanceDecl.ID(d)!)!.instance
    default:
      unexpected(d, in: program.ast)
    }
  }

  /// If `d` is a trait extension, returns the trait that it extends; returns `nil` otherwise.
  private mutating func extendedTrait(_ d: ExtensionDecl.ID) -> TraitType? {
    guard
      let t = GenericTypeParameterType(uncheckedType(of: d)),
      let u = TraitDecl.ID(program[t.decl].scope)
    else { return nil }
    return TraitType(u, ast: program.ast)
  }

  // MARK: Evaluation

  /// Evaluates and returns the value of `e`, which is an annotation that may contain wildcards or
  /// elided generic arguments, using `hint` for context and updating `obligations` with new goals.
  private mutating func evalPartialTypeAnnotation(
    _ e: AnyExprID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType? {
    let t = inferredType(of: e, withHint: hint, updating: &obligations)
    return ensureValidTypeAnnotation(e, inferredAs: t)
  }

  /// Evaluates and returns the value of `e`, which is a type annotation.
  private mutating func evalTypeAnnotation(_ e: AnyExprID) -> AnyType {
    let t = checkedType(of: e)
    return ensureValidTypeAnnotation(e, inferredAs: t) ?? .error
  }

  /// Evaluates and returns the generic arguments in `s`.
  ///
  /// Wildcards are evaluated as fresh variables to support partial type inference. These may
  /// be substituted by either a type or a value.
  private mutating func evalGenericArguments(_ s: [LabeledArgument]) -> [CompileTimeValue] {
    var result: [CompileTimeValue] = []
    for a in s {
      result.append(evalGenericArgument(a))
    }
    return result
  }

  /// Evaluates and returns the value of `e`.
  private mutating func evalGenericArgument(_ e: LabeledArgument) -> CompileTimeValue {
    if e.value.kind == WildcardExpr.self {
      return .type(^freshVariable())
    }

    let t = checkedType(of: e.value)
    if let u = denotationAsType(expressionTyped: t) {
      return .type(u)
    } else {
      return denotation(of: e.value)
    }
  }

  /// Evaluates `e` as a buffer type expression, having inferred that the type of the buffer's
  /// elements is `t`.
  private mutating func evalBufferTypeExpression(
    _ e: SubscriptCallExpr.ID, havingInferredElementType t: AnyType
  ) -> MetatypeType {
    let n = program[e].arguments[0].value
    let i = program.ast.coreType("Int")!
    let j = checkedType(of: n, withHint: ^i)

    // Bail out if the type of the argument isn't `Hylo.Int`.
    if j != i {
      report(.error(expected: ^i, found: j, at: program[n].site))
      return MetatypeType(of: BufferType(t, ^ConcreteTerm(wrapping: 0)))
    } else {
      let v = denotation(of: n).asTerm!
      return MetatypeType(of: BufferType(t, v))
    }
  }

  /// Ensures that `t` is a valid type for an annotation and returns its meaning iff it is;
  /// otherwise, returns `nil`.
  private mutating func ensureValidTypeAnnotation(
    _ e: AnyExprID, inferredAs t: AnyType
  ) -> AnyType? {
    if let u = denotationAsType(expressionTyped: t) {
      return u
    } else {
      report(.error(typeExprDenotesValue: e, in: program.ast))
      return nil
    }
  }

  /// Returns the value expressed by an expression of type `t` iff that value is a type.
  private func denotationAsType(expressionTyped t: AnyType) -> AnyType? {
    switch t.base {
    case let u as MetatypeType:
      return u.instance
    case is ErrorType, is NamespaceType, is TraitType:
      return t
    default:
      return nil
    }
  }

  /// Returns the value expressed by `e`.
  private func denotation(of e: AnyExprID) -> CompileTimeValue {
    switch e.kind {
    case IntegerLiteralExpr.self:
      return denotation(of: IntegerLiteralExpr.ID(e)!)
    case NameExpr.self:
      return denotation(of: NameExpr.ID(e)!)
    default:
      unexpected(e, in: program.ast)
    }
  }

  /// Returns the value expressed by `e`
  private func denotation(of e: IntegerLiteralExpr.ID) -> CompileTimeValue {
    if cache.local.exprType[e]! == program.ast.coreType("Int")! {
      return .term(^ConcreteTerm(wrapping: Int(program[e].value)!))
    } else {
      UNIMPLEMENTED("arbitrary compile-time literals")
    }
  }

  /// Returns the value expressed by `e`
  private func denotation(of e: NameExpr.ID) -> CompileTimeValue {
    guard let d = cache.local.referredDecl[e] else {
      return .term(^ErrorTerm())
    }

    if let p = d.decl.flatMap(GenericParameterDecl.ID.init(_:)) {
      return .term(^GenericTermParameter(p, ast: program.ast))
    } else {
      UNIMPLEMENTED("denotation of \(e.kind)")
    }
  }

  /// Evaluates and returns the qualification of `e`, which is a type annotation.
  private mutating func evalTypeQualification(of e: NameExpr.ID) -> AnyType? {
    switch program[e].domain {
    case .explicit(let q):
      return evalTypeAnnotation(q)
    case .implicit:
      report(.error(notEnoughContextToResolveMember: program[e].name))
      return .error
    case .none, .operand:
      unreachable()
    }
  }

  /// Returns the inferred qualification of `e`, using `implicitQualification` to resolve implicit
  /// domains and updating `obligations`.
  public mutating func inferredQualification(
    of e: NameExpr.ID, implicitlyIn implicitQualification: AnyType?,
    updating obligations: inout ProofObligations
  ) -> AnyType? {
    switch program[e].domain {
    case .explicit(let q):
      let h = program.ast.isImplicitlyQualified(q) ? implicitQualification : nil
      return inferredType(of: q, withHint: h, updating: &obligations)
    case .implicit:
      return implicitQualification
    case .none, .operand:
      unreachable()
    }
  }

  /// Evaluates and returns the parameter annotations of `e`.
  private mutating func evalParameterAnnotations(
    of e: ArrowTypeExpr.ID
  ) -> [CallableTypeParameter] {
    var result: [CallableTypeParameter] = []
    for p in program[e].parameters {
      let t = evalParameterAnnotation(p.type)
      result.append(.init(label: p.label?.value, type: t))
    }
    return result
  }

  /// Evaluates and returns the value of `e`.
  private mutating func evalParameterAnnotation(_ e: ParameterTypeExpr.ID) -> AnyType {
    let t = evalTypeAnnotation(program[e].bareType)

    if program[e].isAutoclosure {
      let s = program[program[e].bareType].site
      guard let u = ArrowType(t), u.inputs.isEmpty else {
        report(.error(autoclosureExpectsEmptyEnvironment: s, given: t))
        return .error
      }
    }

    return ^ParameterType(program[e].convention.value, t, isAutoclosure: program[e].isAutoclosure)
  }

  /// Evaluates and returns the return type annotation of `d`.
  ///
  /// The value of `d`'s explicit return type annotation is returned if it is defined. Otherwise,
  /// a fresh type variable is returned if `d` appears in an expression context (i.e., `d` is the
  /// underlying declaration of a lambda). Otherwise, `.void` is returned.
  private mutating func evalReturnTypeAnnotation(of d: FunctionDecl.ID) -> AnyType {
    if let o = program[d].output {
      return evalTypeAnnotation(o)
    } else if program[d].isInExprContext {
      return ^freshVariable()
    } else {
      return .void
    }
  }

  /// Evaluates and returns the return type annotation of `d`.
  ///
  /// The value of `d`'s explicit return type annotation is returned if it is defined. Otherwise,
  /// `.void` is returned.
  private mutating func evalReturnTypeAnnotation(of d: MethodDecl.ID) -> AnyType {
    if let o = program[d].output {
      return evalTypeAnnotation(o)
    } else {
      return .void
    }
  }

  /// Evaluates the traits in `composition`, returning a sequence of pairs `(n, t)` where `n` is
  /// an expression in `composition` and `t` the corresponding trait.
  ///
  /// The returned sequence contains an element for each valid trait expression in `composition`.
  /// A diagnostic is reported each invalid expression.
  private mutating func evalTraitComposition<S: Sequence<NameExpr.ID>>(
    _ composition: S
  ) -> [(name: NameExpr.ID, trait: TraitType)] {
    var result: [(name: NameExpr.ID, trait: TraitType)] = []

    for n in composition {
      let t = evalTypeAnnotation(AnyExprID(n))
      if let u = TraitType(t) {
        result.append((n, u))
      } else if t[.hasError] {
        // Error already diagnosed.
      } else {
        report(.error(conformanceToNonTraitType: t, at: program[n].site))
      }
    }

    return result
  }

  /// Evaluates and returns `e`, which is a type annotation describing the subject of an extension
  /// or a bound in an existential type, along with its associated constraints.
  private mutating func eval(existentialBound e: AnyExprID) -> (AnyType, Set<GenericConstraint>) {
    // Name expressions may contain sugared constraints. Others cannot.
    if let n = NameExpr.ID(e) {
      return eval(existentialBound: n)
    } else {
      let t = evalTypeAnnotation(e)
      assert(!(t.base is BoundGenericType), "unexpected bound generic type")
      return (t, [])
    }
  }

  /// Evaluates and returns `e`, which is a type annotation describing the subject of an extension
  /// or a bound in an existential type, along with its associated constraints.
  ///
  /// When a name expression describes the subject of an extension or a bound an existential bound,
  /// generic parameters are interpreted as sugared constraints that would otherwise be defined in
  /// a where clause. For example, in `conformance Array<Int>: P {}`, the extended type is `Array`
  /// and `Int` is interpreted as a constraint on `Array`'s generic parameter.
  private mutating func eval(
    existentialBound e: NameExpr.ID
  ) -> (AnyType, Set<GenericConstraint>) {
    let resolution = resolve(e) { (me, n) in
      me.evalTypeQualification(of: n)
    }

    switch resolution {
    case .failed:
      return error()

    case .canceled:
      report(.error(noContextToResolve: program[e].name.value, at: program[e].name.site))
      return error()

    case .done(let prefix, let suffix):
      // Nominal type expressions shall not be overloaded.
      if !suffix.isEmpty {
        cache.write(.error, at: \.exprType[e])
        return error()
      }

      var t: AnyType?
      for n in prefix {
        t = bindExistentialBoundComponent(n)
        if t == nil { return error() }
      }
      return (t!, [])
    }

    /// Assigns `e` to an error and returns `(.error, [])`.
    func error() -> (AnyType, Set<GenericConstraint>) {
      cache.write(.error, at: \.exprType[e])
      return (.error, [])
    }
  }

  /// Binds `n` to its declaration and returns its type.
  private mutating func bindExistentialBoundComponent(
    _ n: NameResolutionResult.ResolvedComponent
  ) -> AnyType? {
    guard let pick = n.candidates.uniqueElement else {
      report(.error(ambiguousUse: n.component, in: program.ast))
      return nil
    }

    cache.write(pick.reference, at: \.referredDecl[n.component])

    switch pick.type.base {
    case is BuiltinType, is NamespaceType, is TraitType:
      cache.write(pick.type, at: \.exprType[n.component])
      return pick.type

    case let m as MetatypeType:
      cache.write(pick.type, at: \.exprType[n.component])

      // Arguments to bound generic types desugar like where clauses. No constraint is created when
      // an argument refers to its corresponding parameter, unless the `d` is nested in the scope
      // where that parameter is introduced.
      if let u = BoundGenericType(m.instance) {
        for (p, a) in u.arguments {
          if GenericTypeParameterType(a.asType!)?.decl != p { UNIMPLEMENTED() }
        }
        return u.base
      } else {
        return m.instance
      }

    default:
      report(.error(typeExprDenotesValue: n.component, in: program.ast))
      return nil
    }
  }

  /// Evaluates `e`, which expresses the bounds of an existential type expression, returning the
  /// type of each bound and all associated constraints.
  private mutating func eval(
    existentialInterface e: [NameExpr.ID]
  ) -> (ExistentialType.Interface, Set<GenericConstraint>) {
    guard let (head, tail) = e.headAndTail else { return (.traits([]), []) }

    if tail.isEmpty {
      let (i, cs) = eval(existentialBound: AnyExprID(head))
      if let t = TraitType(i) {
        return (.traits([t]), cs)
      } else {
        return (.generic(i), cs)
      }
    }

    var bounds: Set<TraitType> = []
    var constraints: Set<GenericConstraint> = []

    for n in e {
      let (i, cs) = eval(existentialBound: AnyExprID(n))

      if let u = TraitType(i) {
        bounds.insert(u)
        constraints.formUnion(cs)
      } else if i[.hasError] {
        // Error already diagnosed.
      } else {
        report(.error(notATrait: i, at: program[n].site))
      }
    }

    return (.traits(bounds), constraints)
  }

  // MARK: Name lookup

  /// Returns the declarations that introduce `name` and are exposed to `scopeOfUse`.
  ///
  /// Declarations are lookup up qualified in `nominalScope` if it isn't `nil`. Otherwise, they are
  /// looked up unqualified from `scopeOfuse`. Access modifiers are ignored.
  private mutating func lookup(
    _ name: SourceRepresentable<Name>, memberOf nominalScope: AnyType?,
    exposedTo scopeOfuse: AnyScopeID
  ) -> [AnyDeclID] {
    var matches = Set<AnyDeclID>()
    if let t = nominalScope {
      matches = lookup(name.value.stem, memberOf: t, exposedTo: scopeOfuse)
    } else {
      matches = lookup(unqualified: name.value.stem, in: scopeOfuse)
    }
    return matches.compactMap({ decl(in: $0, named: name.value) })
  }

  /// Returns the declarations that introduce an entity with given `stem` exposed to `scopeOfUse`
  /// without qualification.
  ///
  /// - Requires: The imports of the module containing `scopeOfUse` have been configured.
  private mutating func lookup(
    unqualified stem: String, in scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    var matches = Set<AnyDeclID>()
    var containingFile: TranslationUnit.ID? = nil
    var containingModule: ModuleDecl.ID? = nil

    for s in program.scopes(from: scopeOfUse) {
      if let u = TranslationUnit.ID(s) {
        containingFile = u
      } else if let m = ModuleDecl.ID(s) {
        containingModule = m
      }

      // Gather declarations of the identifier in the current scope; we can assume we've got no
      // non-overloadable candidate in `matches` yet.
      let newMatches = lookup(stem, in: s, exposedTo: scopeOfUse)
      if insert(newMatches: newMatches, into: &matches) {
        return matches
      }
    }

    // Handle references to the containing module.
    if matches.isEmpty && (program[containingModule!].baseName == stem) {
      return [AnyDeclID(containingModule!)]
    }

    // Handle references to imported symbols.
    if let u = containingFile, let fileImports = cache.local.imports[u] {
      for m in fileImports {
        if program[m].baseName == stem {
          matches.insert(AnyDeclID(m))
        } else {
          matches.formUnion(names(introducedIn: m)[stem, default: []])
        }
      }
    }

    return matches
  }

  /// Merges `newMatches` into `partialResult`, returning `true` iff a non-overloadable declaration
  /// was inserted.
  ///
  /// Bindings under checking are not inserted, thus preventing initializing expressions from
  /// referring to the left hand side of a binding initialization (e.g., `let x = x`).
  ///
  /// - Requires: `partialResult` doesn't contain any non-overloadable declaration.
  private mutating func insert(
    newMatches: Set<AnyDeclID>, into partialResult: inout Set<AnyDeclID>
  ) -> Bool {
    var hasNonOverloadable = false
    for m in newMatches {
      if (m.kind == VarDecl.self) && cache.declsUnderChecking.contains(m) { continue }
      partialResult.insert(m)
      hasNonOverloadable = hasNonOverloadable || !m.isOverloadable
    }
    return hasNonOverloadable
  }

  /// Returns the declarations that introduce a name with given `stem` in the declaration space of
  /// `lookupContext` and are exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, in lookupContext: AnyScopeID, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    switch lookupContext.kind {
    case ProductTypeDecl.self:
      let t = ProductType(NodeID(lookupContext)!, ast: program.ast)
      return lookup(stem, memberOf: ^t, exposedTo: scopeOfUse)
    case TraitDecl.self:
      let t = TraitType(NodeID(lookupContext)!, ast: program.ast)
      return lookup(stem, memberOf: ^t, exposedTo: scopeOfUse)
    case ConformanceDecl.self:
      let d = ConformanceDecl.ID(lookupContext)!
      return lookup(stem, in: d, exposedTo: scopeOfUse)
    case ExtensionDecl.self:
      let d = ExtensionDecl.ID(lookupContext)!
      return lookup(stem, in: d, exposedTo: scopeOfUse)
    case TypeAliasDecl.self:
      let d = TypeAliasDecl.ID(lookupContext)!
      return lookup(stem, in: d, exposedTo: scopeOfUse)
    default:
      return names(introducedIn: lookupContext)[stem, default: []]
    }
  }

  /// Returns the declarations that introduce a name with given `stem` in the declaration space of
  /// `lookupContext` and are exposed to `scopeOfUse`.
  private mutating func lookup<T: TypeExtendingDecl>(
    _ stem: String, in lookupContext: T.ID, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    let extended = uncheckedType(of: lookupContext)

    if let t = GenericTypeParameterType(extended), isTraitReceiver(t), stem == "Self" {
      // "Self" in the context of a trait extension denotes that trait's receiver.
      return [AnyDeclID(t.decl)]
    } else {
      var matches = names(introducedIn: lookupContext)[stem, default: []]
      matches.formUnion(lookup(stem, memberOf: extended, exposedTo: scopeOfUse))
      return matches
    }
  }

  /// Returns the declarations that introduce a name with given `stem` in the declaration space of
  /// `lookupContext` and are exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, in lookupContext: TypeAliasDecl.ID, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    // We can't re-enter `uncheckedType(of:)` if the aliased type of `lookupContext` is being
    // resolved but its generic parameters can be lookep up already.
    if cache.uncheckedType[lookupContext] == .inProgress {
      return names(introducedIn: lookupContext)[stem, default: []]
    }

    let t = uncheckedType(of: lookupContext)
    return lookup(stem, memberOf: t, exposedTo: scopeOfUse)
  }

  /// Returns the declarations that introduce a name with given `stem` as member of `nominalScope`
  /// and are exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, memberOf nominalScope: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    switch nominalScope.base {
    case is ErrorType:
      return []
    case let t as AssociatedTypeType:
      return lookup(stem, memberOf: t, exposedTo: scopeOfUse)
    case let t as BoundGenericType:
      return lookup(stem, memberOf: t.base, exposedTo: scopeOfUse)
    case let t as ConformanceLensType:
      return lookup(stem, memberOf: ^t.lens, exposedTo: scopeOfUse)
    case let t as ExistentialType:
      return lookup(stem, memberOf: t, exposedTo: scopeOfUse)
    case let t as RemoteType:
      return lookup(stem, memberOf: t.bareType, exposedTo: scopeOfUse)
    case let t as GenericTypeParameterType:
      return lookup(stem, memberOf: t, exposedTo: scopeOfUse)
    case let t as TypeAliasType:
      return lookup(stem, memberOf: t, exposedTo: scopeOfUse)
    default:
      break
    }

    let key = Cache.TypeLookupKey(nominalScope, in: scopeOfUse)
    if let m = cache.scopeToMembers[key]?[stem] {
      return m
    }

    var matches: Set<AnyDeclID>
    defer { cache.scopeToMembers[key, default: [:]][stem] = matches }

    switch nominalScope.base {
    case let t as ProductType:
      matches = names(introducedIn: t.decl)[stem, default: []]
    case let t as ModuleType:
      matches = names(introducedIn: t.decl)[stem, default: []]
    case let t as NamespaceType:
      matches = names(introducedIn: t.decl)[stem, default: []]
    case let t as TraitType:
      matches = names(introducedIn: t.decl)[stem, default: []]
    default:
      matches = []
    }

    if matches.allSatisfy(\.isOverloadable) {
      matches.formUnion(lookup(stem, inExtensionsOf: nominalScope, exposedTo: scopeOfUse))
    }

    return matches
  }

  /// Returns the declarations that introduce a name with given `stem` as member of `nominalScope`
  /// and are exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, memberOf nominalScope: AssociatedTypeType,
    exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    var matches = Set<AnyDeclID>()
    for t in conformedTraits(of: nominalScope, in: scopeOfUse) {
      matches.formUnion(lookup(stem, memberOf: ^t, exposedTo: scopeOfUse))
    }
    return matches
  }

  /// Returns the declarations that introduce a name with given `stem` as member of`nominalScope`
  /// and exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, memberOf nominalScope: ExistentialType, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    // Declarations in extensions of existential types shadow their existential APIs.
    let matches = lookup(stem, inExtensionsOf: ^nominalScope, exposedTo: scopeOfUse)
    if !matches.isEmpty {
      return matches
    }

    // Search in the existential API.
    switch nominalScope.interface {
    case .traits(let s):
      return s.reduce(into: Set<AnyDeclID>()) { (r, t) in
        r.formUnion(lookup(stem, memberOf: ^t, exposedTo: scopeOfUse))
      }
    case .generic(let t):
      return lookup(stem, memberOf: t, exposedTo: scopeOfUse)
    case .metatype:
      return []
    }
  }

  /// Returns the declarations that introduce a name with given `stem` as member of `nominalScope`
  /// and are exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, memberOf nominalScope: GenericTypeParameterType,
    exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    var matches = Set<AnyDeclID>()
    for t in conformedTraits(of: nominalScope, in: scopeOfUse) {
      matches.formUnion(lookup(stem, memberOf: ^t, exposedTo: scopeOfUse))
    }
    return matches
  }

  /// Returns the declarations that introduce a name with given `stem` as member of `nominalScope`
  /// and are exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, memberOf nominalScope: TypeAliasType, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    if let d = names(introducedIn: nominalScope.decl)[stem] {
      return d
    } else if program[nominalScope.decl].genericParameters.isEmpty {
      return lookup(stem, memberOf: nominalScope.aliasee.value, exposedTo: scopeOfUse)
    } else {
      let t = MetatypeType(uncheckedType(of: nominalScope.decl))!
      let a = TypeAliasType(t.instance)!.aliasee.value
      return lookup(stem, memberOf: a, exposedTo: scopeOfUse)
    }
  }

  /// Returns the declarations that introduce a name with given `stem` in extensions of
  /// `nominalScope` and are exposed to `scopeOfUse`.
  private mutating func lookup(
    _ stem: String, inExtensionsOf nominalScope: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> Set<AnyDeclID> {
    var matches = Set<AnyDeclID>()

    // Look for members declared in extensions.
    for i in extensions(of: nominalScope, exposedTo: scopeOfUse) {
      matches.formUnion(names(introducedIn: AnyScopeID(i)!)[stem, default: []])
    }

    // Look for members declared inherited by conformance/refinement.
    for t in conformedTraits(of: nominalScope, in: scopeOfUse) where nominalScope != t {
      // TODO: Read source of conformance to disambiguate associated names
      let newMatches = lookup(stem, memberOf: ^t, exposedTo: scopeOfUse)

      // Generic parameters introduced by traits are not inherited.
      matches.formUnion(newMatches.filter({ $0.kind != GenericParameterDecl.self }))
    }

    return matches
  }

  /// Returns the declarations of an operator specified operator that are visible in `scopeOfUse`.
  private func lookup<T: ScopeID>(
    operator operatorName: Identifier, used notation: OperatorNotation,
    in scopeOfUse: T
  ) -> [OperatorDecl.ID] {
    let currentModule = program.module(containing: scopeOfUse)
    if let oper = lookup(operator: operatorName, used: notation, in: currentModule) {
      return [oper]
    }

    return program.ast.modules.compactMap { (m) -> OperatorDecl.ID? in
      if m == currentModule { return nil }
      return lookup(operator: operatorName, used: notation, in: m)
    }
  }

  /// Returns the declaration of the specified operator that are visible in `scopeOfUse`, or `nil`
  /// if no such operator is declared in `scopeOfUse`.
  private func lookup(
    operator operatorName: Identifier, used notation: OperatorNotation,
    in scopeOfUse: ModuleDecl.ID
  ) -> OperatorDecl.ID? {
    for d in program[scopeOfUse].decls.withoutExtensions where d.kind == OperatorDecl.self {
      let o = OperatorDecl.ID(d)!
      if (program[o].notation.value == notation) && (program[o].name.value == operatorName) {
        return o
      }
    }
    return nil
  }

  /// Returns the stem and declaration of `c`, which occurs in `d`, or `nil` if either `c` doesn't
  /// have to be captured or lookup failed.
  private mutating func lookupImplicitCapture<T: Decl & LexicalScope>(
    _ c: NameExpr.ID, occurringIn d: T.ID
  ) -> (stem: String, decl: AnyDeclID)? {
    let n = program[c].name
    let s = AnyScopeID(d)
    var candidates = lookup(unqualified: n.value.stem, in: program[c].scope)
    candidates.removeAll(where: { isCaptured(referenceTo: $0, occurringIn: s) })
    if candidates.isEmpty { return nil }

    guard let pick = candidates.uniqueElement else {
      report(.error(cannotCaptureOverloadedNameImplicitly: n))
      return nil
    }

    if program.isMember(pick) {
      return ("self", lookup(unqualified: "self", in: s).uniqueElement!)
    } else {
      return (n.value.stem, pick)
    }
  }

  /// Returns the names introduced in `s`.
  ///
  /// The returned table only contains names whose declaration are lexically contained directly in
  /// `s`. Names introduced by declarations in extensions or inherited by conformance are looked up
  /// using `lookup(_:memberOf:exposedTo:)`.
  private mutating func names<T: ScopeID>(introducedIn s: T) -> Cache.LookupTable {
    // Check if work has to be done.
    if let table = cache.scopeToNames[AnyScopeID(s)] { return table }

    var table: Cache.LookupTable
    defer { cache.scopeToNames[AnyScopeID(s)] = table }

    // Names at module scope are introduced in the module's files.
    if let module = ModuleDecl.ID(s) {
      table = program[module].sources.reduce(into: [:]) { (t, s) in
        t.merge(names(introducedIn: s), uniquingKeysWith: { (l, _) in l })
      }
      return table
    } else {
      table = [:]
    }

    // Nothing to do if the scope contains no declaration.
    let decls = program[AnyScopeID(s)!].decls
    if decls.isEmpty { return [:] }

    for d in decls {
      switch d.kind {
      case FunctionDecl.self:
        guard let i = program[FunctionDecl.ID(d)!].identifier?.value else { continue }
        table[i, default: []].insert(d)
      case InitializerDecl.self:
        table["init", default: []].insert(d)
        table["new", default: []].insert(d)
      case MethodDecl.self:
        table[program[MethodDecl.ID(d)!].identifier.value, default: []].insert(d)
      case SubscriptDecl.self:
        let i = program[SubscriptDecl.ID(d)!].identifier?.value ?? "[]"
        table[i, default: []].insert(d)
      default:
        // Note: operator declarations are not considered during standard name lookup.
        break
      }

      if let e = (program.ast[d] as? SingleEntityDecl) {
        table[e.baseName, default: []].insert(d)
        continue
      }
    }

    return table
  }

  /// Returns the declarations extending `subject` exposed to `scopeOfUse`.
  ///
  /// - Returns: The declarations extending `subject`, which all conform to `TypeExtendingDecl`.
  private mutating func extensions(
    of subject: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> [AnyDeclID] {
    let t = canonical(subject, in: scopeOfUse)

    switch t.base {
    case let u as BoundGenericType:
      // Extensions of bound generic types are looked up without the generic arguments.
      return extensions(of: u.base, exposedTo: scopeOfUse)

    case let u as TraitType:
      // Extensions of traits are looked up by their receiver parameters.
      let p = ^GenericTypeParameterType(selfParameterOf: u.decl, in: program.ast)
      return extensions(of: p, exposedTo: scopeOfUse)

    default:
      return _extensions(of: t, exposedTo: scopeOfUse)
    }
  }

  /// Returns the declarations extending `subject` exposed to `scopeOfUse`.
  ///
  /// - Requires: `subject` is canonical.
  private mutating func _extensions(
    of subject: AnyType, exposedTo scopeOfUse: AnyScopeID
  ) -> [AnyDeclID] {
    let key = Cache.TypeLookupKey(subject, in: scopeOfUse)
    if let result = cache.typeToExtensions[key] { return result }

    var partialResult: [AnyDeclID] = []
    defer { cache.typeToExtensions[key] = partialResult }

    var s = scopeOfUse
    while true {
      if let u = TranslationUnit.ID(s) {
        for m in imports(exposedTo: u) {
          appendExtensions(declaredIn: AnyScopeID(m), extending: subject, to: &partialResult)
        }
        return partialResult
      } else {
        appendExtensions(declaredIn: s, extending: subject, to: &partialResult)
      }

      if let p = program.nodeToScope[s] {
        s = p
      } else {
        return partialResult
      }
    }
  }

  /// Adds the declarations in `s` that extends `t` to `partialResult`.
  ///
  /// - Requires: `t` is canonical.
  private mutating func appendExtensions(
    declaredIn s: AnyScopeID, extending t: AnyType, to partialResult: inout [AnyDeclID]
  ) {
    // This method implements extension binding, which consists of associating an extension with
    // the type that it extends. Ideally, we would like to complete extension binding before
    // answering qualified name lookup requests, because determining whether `Bar` is member of
    // `Foo` requires looking in all extensions of `Foo`. Unfortunately, evaluating the expression
    // type expressions may require qualified name lookup so we have to bind extensions lazily.
    //
    // To find the extensions of a type T, we have to resolve the type of each unbound extension
    // and then check if that type is T. We avoid recursion during name lookup by ignoring the
    // extensions that occurred on the stack. That's fine because extensions can't extend a type
    // they declare.
    //
    // We minimize the number of linear passes we make by eagerly binding the extensions that we
    // visit, regardless of the type that they extend. That way, the result of future calls to this
    // method for a different type have a chance to be cached already.

    // Nothing to do if the scope doesn't contain any extension.
    let n = program[s].decls.extensions.count
    if n == 0 { return }

    // We swap the contents of the cache with `c` to avoid unnecessary copies.
    var c: Cache.ScopeExtensionCache? = nil
    swap(&c, &cache.scopeToTypeToExtensions[s])
    if c == nil { c = .init(count: n) }

    // Faster path: we've bound all extensions in `s`; we know which ones extend `t`.
    if c!.unbound.allFalse {
      if let e = c!.typeToExtension[t] {
        partialResult.append(contentsOf: e)
      }
      swap(&c, &cache.scopeToTypeToExtensions[s])
      return
    }

    // Slower path: we must complete extension binding.
    for (i, d) in program[s].decls.extensions.enumerated() where c!.unbound[i] {
      switch cache.uncheckedType[d] {
      case .some(.inProgress):
        // Skip declarations that are already on the checker's stack.
        continue

      case .some(.computed(let extended)):
        // Extended type was already computed; no need to deal with re-entrency.
        let x = canonical(extended, in: s)
        c!.typeToExtension[x, default: []].append(d)

      case .none:
        // The type of the extension is not known yet; we have to compute it. That may cause a
        // re-entrant call into the current method, so we have to commit the state of our cache.
        swap(&c, &cache.scopeToTypeToExtensions[s])
        let extended = canonical(uncheckedType(of: d), in: s)
        swap(&c, &cache.scopeToTypeToExtensions[s])
        c!.typeToExtension[extended, default: []].append(d)
      }

      assert(c!.unbound[i])
      c!.unbound[i] = false
    }

    partialResult.append(contentsOf: c!.typeToExtension[t, default: []])
    swap(&c, &cache.scopeToTypeToExtensions[s])
  }

  /// Returns `d` if it has name `n`, otherwise the implementation of `d` with name `n` or `nil`
  /// if no such implementation exists.
  ///
  /// - Requires: The base name of `d` is equal to `n.stem`
  private mutating func decl(in d: AnyDeclID, named n: Name) -> AnyDeclID? {
    if !n.labels.isEmpty && (n.labels != labels(d)) { return nil }
    if let x = n.notation, x != operatorNotation(d) { return nil }

    // If the looked up name has an introducer, return the corresponding implementation.
    return n.introducer.map(default: d) { (k) in
      MethodDecl.ID(d)
        .flatMap({ (m) in program.ast.implementation(k, of: m) })
        .flatMap(AnyDeclID.init(_:))
    }
  }

  /// Returns the labels of `d`s name.
  ///
  /// Only function, method, or subscript declarations may have labels. This method returns `[]`
  /// for any other declaration.
  private mutating func labels(_ d: AnyDeclID) -> [String?] {
    let ast = program.ast
    switch d.kind {
    case FunctionDecl.self:
      return labels(FunctionDecl.ID(d)!)
    case InitializerDecl.self:
      return labels(InitializerDecl.ID(d)!)
    case MethodDecl.self:
      return ast[ast[MethodDecl.ID(d)!].parameters].map(\.label?.value)
    case SubscriptDecl.self:
      return ast[ast[SubscriptDecl.ID(d)!].parameters].map(\.label?.value)
    default:
      return []
    }
  }

  /// Returns the labels of `d`s name.
  private func labels(_ d: FunctionDecl.ID) -> [String?] {
    program.ast[program[FunctionDecl.ID(d)!].parameters].map(\.label?.value)
  }

  /// Returns the labels of `d`s name.
  private mutating func labels(_ d: InitializerDecl.ID) -> [String?] {
    if let t = ArrowType(uncheckedType(of: d)) {
      return Array(t.labels)
    } else if !program[d].isMemberwise {
      return ["self"] + program.ast[program[d].parameters].map(\.label?.value)
    }

    let p = ProductTypeDecl.ID(program[d].scope)!
    return program[p].members.reduce(into: ["self"]) { (l, m) in
      guard let b = BindingDecl.ID(m) else { return }
      for (_, x) in program.ast.names(in: program[b].pattern) {
        l.append(program[x].decl.baseName)
      }
    }
  }

  /// Returns the operator notation of `d`'s name, if any.
  private func operatorNotation(_ d: AnyDeclID) -> OperatorNotation? {
    switch d.kind {
    case FunctionDecl.self:
      return program[FunctionDecl.ID(d)!].notation?.value
    case MethodDecl.self:
      return program[MethodDecl.ID(d)!].notation?.value
    default:
      return nil
    }
  }

  /// If `s` is contained in a type extending declaration, returns the scope extended by that
  /// declaration; returns `nil` otherwise.
  private mutating func bridgedScope<S: ScopeID>(of s: S) -> AnyScopeID? {
    switch s.kind {
    case ConformanceDecl.self:
      return scopeExtended(by: ConformanceDecl.ID(s)!)
    case ExtensionDecl.self:
      return scopeExtended(by: ExtensionDecl.ID(s)!)
    case ModuleDecl.self:
      return nil
    default:
      return bridgedScope(of: program[s].scope)
    }
  }

  /// Returns the scope of the declaration extended by `d`, if any.
  mutating func scopeExtended<T: TypeExtendingDecl>(by d: T.ID) -> AnyScopeID? {
    let t = uncheckedType(of: d)
    switch t.base {
    case let u as GenericTypeParameterType where isTraitReceiver(u):
      return program[u.decl].scope
    case let u as ProductType:
      return AnyScopeID(u.decl)
    case let u as TypeAliasType:
      return AnyScopeID(u.decl)
    default:
      return nil
    }
  }

  /// Returns the innermost nominal scope in which `d` is contained, if any.
  private mutating func nominalParent(of d: AnyDeclID) -> AnyScopeID? {
    guard let p = program.nodeToScope[d] else {
      assert(d.kind == ModuleDecl.self)
      return nil
    }

    switch p.kind {
    case ModuleDecl.self, NamespaceDecl.self, ProductTypeDecl.self, TypeAliasDecl.self:
      return p
    case ConformanceDecl.self:
      return scopeExtended(by: ConformanceDecl.ID(p)!)
    case ExtensionDecl.self:
      return scopeExtended(by: ExtensionDecl.ID(p)!)
    case MethodDecl.self:
      return nominalParent(of: AnyDeclID(p)!)
    case SubscriptDecl.self:
      return nominalParent(of: AnyDeclID(p)!)
    case TranslationUnit.self:
      return program.nodeToScope[p]!
    default:
      return nil
    }
  }

  /// Returns `true` iff a qualified reference to `d` is visible in `scopeOfUse`.
  ///
  /// Qualified name lookup may "see" a declaration `d` iff one the following holds:
  /// - `d` is declared public.
  /// - `d` is a trait requirement.
  /// - `d` is declared internal and `scopeOfUse` is in the same scope.
  /// - `d` is declared private and the innermost scope enclosing `d` also encloses `scopeOfUse`.
  private mutating func isAccessibleWithQualification(
    _ d: AnyDeclID, in scopeOfUse: AnyScopeID
  ) -> Bool {
    if let v = VarDecl.ID(d) {
      return isAccessibleWithQualification(AnyDeclID(program[v].binding), in: scopeOfUse)
    } else if d.isBundleImpl {
      return isAccessibleWithQualification(AnyDeclID(program[d].scope)!, in: scopeOfUse)
    } else if program.isRequirement(d) {
      return true
    }

    // Note: direct access to the AST is necessary to support the cast to `ExposableDecl`.
    let modifier = (program.ast[d] as? ExposableDecl)?.accessModifier.value

    if modifier == .public {
      return true
    } else if !program.areInSameModule(d, scopeOfUse) {
      return false
    } else if modifier == .internal {
      return true
    } else if let p = nominalParent(of: d) {
      return isNotionallyContained(scopeOfUse, in: p)
    } else {
      return d.kind == ModuleDecl.self
    }
  }

  /// Returns `true` if `child` is lexically contained in or in an extension of `ancestor`.
  private mutating func isNotionallyContained<T: NodeIDProtocol, U: ScopeID>(
    _ child: T, in ancestor: U
  ) -> Bool {
    if child.rawValue == ancestor.rawValue { return true }

    switch child.kind {
    case ConformanceDecl.self:
      return scopeExtended(by: ConformanceDecl.ID(child)!)
        .map({ $0.rawValue == ancestor.rawValue }) ?? program.isContained(child, in: ancestor)
    case ExtensionDecl.self:
      return scopeExtended(by: ExtensionDecl.ID(child)!)
        .map({ $0.rawValue == ancestor.rawValue }) ?? program.isContained(child, in: ancestor)
    default:
      if let n = program.nodeToScope[child] {
        return isNotionallyContained(n, in: ancestor)
      } else {
        return false
      }
    }
  }

  // MARK: Name resolution

  /// Resolves components of `n` from left to right until all components have been resolved or one
  /// component requires overload resolution.
  ///
  /// If the leftmost component of `n` is non-nominal, `resolveNonNominalPrefix` is called on
  /// `self` and the second component `c` of `n` (which is nominal), returning the type `T` of
  /// `c`'s nominal scope or `nil` if such a type can't be determined. If a type is returned,
  /// name resolution proceeds, looking for `c` as a member of `T`. Otherwise, `.canceled(nil, u)`
  /// is returned, where `u` is the nominal suffix of `n`, starting from `c`.
  private mutating func resolve(
    _ n: NameExpr.ID,
    usedAs purpose: NameUse = .unapplied,
    withNonNominalPrefix resolveNonNominalPrefix: (inout Self, NameExpr.ID) -> AnyType?
  ) -> NameResolutionResult {
    var (unresolved, domain) = program.ast.splitNominalComponents(of: n)

    // Continue iff `name` is prefixed by nominal components only.
    var parent: NameResolutionContext? = nil
    if domain != .none {
      guard let p = resolveNonNominalPrefix(&self, unresolved.last!) else {
        return .canceled(nil, unresolved)
      }

      switch p.base {
      case .error:
        return .failed
      case is TypeVariable:
        return .canceled(p, unresolved)
      default:
        parent = .init(type: p, receiver: .init(domain))
      }
    }

    // Process unresolved components from left to right as long as we don't need contextual
    // information to resolve overload sets.
    var resolved: [NameResolutionResult.ResolvedComponent] = []
    while let component = unresolved.popLast() {
      // `purpose` only applies to the last component.
      let u = unresolved.isEmpty ? purpose : .unapplied
      var candidates = resolve(component, in: parent, usedAs: u)

      // Resolution failed if we found no candidates.
      if candidates.isEmpty { return .failed }

      if candidates.count > 1 {
        candidates = filterResolutionCandidates(candidates, in: program[component].scope)
      }

      // Append the resolved component to the nominal prefix.
      resolved.append(.init(component, candidates))

      // Defer resolution of the remaining name components if there are multiple candidates for
      // the current component or if we found a type variable. Otherwise, configure `parent` to
      // resolve the next name component.
      if (candidates.count > 1) || (candidates[0].type.base is TypeVariable) { break }
      let pick = candidates[0]

      // If the candidate is a metatype, perform the next lookup in its instance.
      let receiver = DeclReference.Receiver.explicit(AnyExprID(component))
      let receiverType = MetatypeType(pick.type)?.instance ?? pick.type
      parent = .init(type: receiverType, arguments: pick.reference.arguments, receiver: receiver)
    }

    precondition(!resolved.isEmpty)
    return .done(resolved: resolved, unresolved: unresolved)
  }

  /// Resolves a single name component `n` being used as `purpose` in `context`.
  private mutating func resolve(
    _ n: NameExpr.ID, in context: NameResolutionContext?, usedAs purpose: NameUse
  ) -> [NameResolutionResult.Candidate] {
    let name = program[n].name

    let arguments = evalGenericArguments(program[n].arguments)
    let candidates = resolve(
      name, specializedBy: arguments,
      in: context, exposedTo: program[n].scope, usedAs: purpose)

    // Diagnose undefined symbols.
    if candidates.elements.isEmpty {
      report(.error(undefinedName: name.value, in: context?.type, at: name.site))
      return []
    }

    // Diagnose symbols with no viable candidates.
    if candidates.viable.isEmpty {
      if let c = candidates.elements.uniqueElement {
        report(c.diagnostics.elements)
      } else {
        let notes = candidates.elements.map { (c) -> Diagnostic in
          let s = c.reference.decl.map(program.ast.siteForDiagnostics(about:))
          let m = c.diagnostics.elements.min(by: Diagnostic.isLoggedBefore)?.message
          return .note(m ?? "candidate not viable", at: s ?? name.site)
        }
        report(.error(noViableCandidateToResolve: name, notes: notes))
      }
      return []
    }

    return candidates.viable.map({ candidates.elements[$0] })
  }

  /// Returns the declarations of `name` exposed to `scopeOfUse` and specialized by `arguments`.
  ///
  /// The return value is a set of candidates, each of which corresponding to one possible way to
  /// resolve `name` to a specific declaration. The declarations are searched with an unqualified
  /// lookup unless `context` is set, in which case they are searched in the declaration space of
  /// `context.type`. The specialization of generic is obtained by appending `arguments` to
  /// `parent.arguments`.
  ///
  /// If `name` resolves to an initializer and `purpose` is `.constructor`, the corresponding
  /// candidate is assigned a constructor type. If `purpose` has call labels, they are used to
  /// filter candidates with different labels.
  mutating func resolve(
    _ name: SourceRepresentable<Name>, specializedBy arguments: [CompileTimeValue],
    in context: NameResolutionContext?, exposedTo scopeOfUse: AnyScopeID, usedAs purpose: NameUse
  ) -> NameResolutionResult.CandidateSet {
    // Built-in symbols are handled separately.
    if context?.type == .builtin(.module) {
      return resolve(builtin: name)
    }

    let isQualified = context != nil

    // Compute the set of all possible matches and filter out those that are inaccessible.
    let allMatches = lookup(name, memberOf: context?.type, exposedTo: scopeOfUse)
    let accessibleMatches = filterAccessible(allMatches)

    // Attempt to resolve a compiler-known alias if there's no match and `name` occurs unqualified.
    if accessibleMatches.isEmpty {
      if !isQualified {
        return resolve(compilerKnownAlias: name, specializedBy: arguments, exposedTo: scopeOfUse)
      } else if !allMatches.isEmpty {
        report(.error(invalidReferenceToInaccessible: allMatches, named: name, in: program.ast))
      }
    }

    // Create declaration references to all candidates.
    var candidates: NameResolutionResult.CandidateSet = []
    for m in accessibleMatches {
      var log = DiagnosticSet()

      let t = resolveType(
        of: m, referredToBy: name, specializedBy: arguments, in: context,
        exposedTo: scopeOfUse, usedAs: purpose,
        reportingDiagnosticsTo: &log)
      guard let (candidateType, specialization, isConstructor) = t else { continue }

      let r = program.makeReference(
        to: m, specializedBy: specialization, memberOf: context, exposedTo: scopeOfUse,
        usedAsConstructor: isConstructor)

      if let sugars = resolve(
        sugared: name,
        memberOf: .init(type: candidateType, arguments: specialization, receiver: .elided(r)),
        exposedTo: scopeOfUse, usedAs: purpose)
      {
        candidates.formUnion(sugars)
        continue
      }

      var deferred: ConstraintSet = []
      forEachConstraint(associatedWith: m, in: scopeOfUse) { (me, c) in
        let k = me.evaluateResolutionConstraint(
          c, associatedWith: name, specializedBy: specialization, in: scopeOfUse,
          reportingDiagnosticsTo: &log)
        if let k = k { deferred.insert(k) }
      }

      candidates.insert(
        .init(reference: r, type: candidateType, constraints: deferred, diagnostics: log))
    }

    if let labels = purpose.labels {
      candidates.filter(accepting: labels)
    }

    return candidates

    /// If `isQualified` is `true`, returns the declarations in `ds` that are accessible with
    /// qualification in `scopeOfUse`. Otherwise, returns `ds`.
    func filterAccessible(_ ds: [AnyDeclID]) -> [AnyDeclID] {
      if !isQualified { return ds }
      let tentative = ds.filter({ isAccessibleWithQualification($0, in: scopeOfUse) })

      if !tentative.isEmpty {
        return tentative
      } else if ds.contains(where: { $0.kind == GenericParameterDecl.self }) {
        let membersOfConformedTraits = conformedTraits(of: context!.type, in: scopeOfUse)
          .map({ lookup(name, memberOf: AnyType($0), exposedTo: scopeOfUse) })
        return filterAccessible(Array(Set(membersOfConformedTraits.joined())))
      } else {
        return []
      }
    }
  }

  /// Returns the declaration of `name` interpreted as a member of the built-in module.
  private mutating func resolve(
    builtin name: SourceRepresentable<Name>
  ) -> NameResolutionResult.CandidateSet {
    if let f = BuiltinFunction(name.value.stem) {
      return [.init(f, makingFreshVariableWith: { freshVariable() })]
    }
    if let t = BuiltinType(name.value.stem) {
      return [.init(t)]
    }
    return []
  }

  /// Returns the declarations of `name` interpreted as a compiler-known type alias (e.g., `Never`
  /// or `Union<A, B>`) specialized by `arguments`, or `nil` if an error occurred.
  private mutating func resolve(
    compilerKnownAlias name: SourceRepresentable<Name>,
    specializedBy arguments: [CompileTimeValue],
    exposedTo scopeOfUse: AnyScopeID
  ) -> NameResolutionResult.CandidateSet {
    // TODO: Check labels and notations.
    switch name.value.stem {
    case "Any":
      return nonGeneric(MetatypeType(of: .any))
    case "Builtin":
      return program.builtinIsVisible(in: scopeOfUse) ? [.builtinModule] : []
    case "Metatype":
      return resolve(metatype: name, specializedBy: arguments)
    case "Never":
      return nonGeneric(MetatypeType(of: .never))
    case "Self":
      return resolveReceiverMetatype(in: scopeOfUse).map(nonGeneric(_:)) ?? []
    case "Union":
      return resolve(union: name, specializedBy: arguments)
    default:
      return []
    }

    /// Returns a singleton containing a reference to `t`, which is not generic.
    func nonGeneric(_ t: MetatypeType) -> NameResolutionResult.CandidateSet {
      if arguments.count > 0 {
        report(.error(argumentToNonGenericType: t.instance, at: name.site))
      }
      return [.compilerKnown(^t)]
    }
  }

  /// Resolves `name` as a reference to a union type specialized by `arguments`.
  private mutating func resolve(
    union name: SourceRepresentable<Name>, specializedBy arguments: [CompileTimeValue]
  ) -> NameResolutionResult.CandidateSet {
    var elements: [AnyType] = []
    for a in arguments {
      guard let t = a.asType else {
        report(.error(valueInUnionTypeAt: name.site))
        return [.compilerKnown(.error)]
      }
      elements.append(t)
    }

    switch arguments.count {
    case 0:
      report(.warning(unionTypeWithZeroElementsAt: name.site))
      return [.compilerKnown(^MetatypeType(of: .never))]
    case 1:
      report(.error(unionTypeWithOneElementAt: name.site))
      return [.compilerKnown(.error)]
    default:
      return [.compilerKnown(^MetatypeType(of: UnionType(elements)))]
    }
  }

  /// Resolves `name` as a reference to a metatype specialized by `arguments`.
  private mutating func resolve(
    metatype name: SourceRepresentable<Name>, specializedBy arguments: [CompileTimeValue]
  ) -> NameResolutionResult.CandidateSet {
    if let a = arguments.uniqueElement {
      let instance = a.asType ?? UNIMPLEMENTED()
      return [.compilerKnown(^MetatypeType(of: MetatypeType(of: instance)))]
    }

    if arguments.isEmpty {
      return [.compilerKnown(^MetatypeType(of: MetatypeType(of: freshVariable())))]
    }

    report(.error(invalidGenericArgumentCountTo: name, found: arguments.count, expected: 1))
    return [.compilerKnown(.error)]
  }

  /// Resolves `name` as a sugared reference to a constructor or nameless subscript declaration or
  /// returns `nil` if `name` isn't a sugar.
  private mutating func resolve(
    sugared name: SourceRepresentable<Name>, memberOf parent: NameResolutionContext,
    exposedTo scopeOfUse: AnyScopeID, usedAs purpose: NameUse
  ) -> NameResolutionResult.CandidateSet? {
    // Nothing to do if `parent.type` is a callable type.
    if parent.type.base is CallableType {
      return nil
    }

    switch purpose {
    case .constructor(let ls), .function(let ls, _):
      guard let t = MetatypeType(parent.type)?.instance else { return nil }
      let n = SourceRepresentable(value: Name(stem: "init"), range: name.site)
      let p = NameResolutionContext(type: t, arguments: parent.arguments, receiver: nil)
      let r = resolve(
        n, specializedBy: [], in: p, exposedTo: scopeOfUse, usedAs: .constructor(labels: ls))
      return r.elements.isEmpty ? nil : r

    case .subscript where !(parent.type.base is MetatypeType):
      let n = SourceRepresentable(value: Name(stem: "[]"), range: name.site)
      let r = resolve(
        n, specializedBy: [], in: parent, exposedTo: scopeOfUse, usedAs: purpose)
      return r.elements.isEmpty ? nil : r

    default:
      return nil
    }
  }

  /// Returns the candidates `cs` that are viable picks for overload resolution in `scopeOfUse`.
  private mutating func filterResolutionCandidates(
    _ cs: [NameResolutionResult.Candidate], in scopeOfUse: AnyScopeID
  ) -> [NameResolutionResult.Candidate] {
    var candidatesByType: [AnyType: [Int]] = [:]
    for (i, c) in cs.enumerated() {
      let t = canonical(c.type, in: scopeOfUse)
      candidatesByType[t, default: []].append(i)
    }

    var result: [NameResolutionResult.Candidate] = []
    for (_, group) in candidatesByType {
      let viable = group.minimalElements { (a, b) in
        guard
          let lhs = cs[a].reference.decl,
          let rhs = cs[b].reference.decl
        else { return nil }
        return compareDepth(lhs, rhs, in: scopeOfUse)
      }
      result.append(contentsOf: viable.map({ (i) in cs[i] }))
    }

    return result
  }

  /// Returns the resolved type of the entity declared by `d` when referred to by `name` with
  /// the given `arguments`, or `nil` if `d` is ill-formed.
  ///
  /// If `d` is generic, `context` determines how to construct its complete list of arguments and
  /// the specialization of the returned type is performed in `scopeOfUse`. Diagnostics of errors
  /// related to the construction of the generic argument list are stored in `log`.
  ///
  /// If `d` declares an initializer and `purpose` is `.constructor`, the returned type is the
  /// constructor form of `d`'s type.
  private mutating func resolveType(
    of d: AnyDeclID,
    referredToBy name: SourceRepresentable<Name>,
    specializedBy arguments: [CompileTimeValue],
    in context: NameResolutionContext?,
    exposedTo scopeOfUse: AnyScopeID,
    usedAs purpose: NameUse,
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) -> (type: AnyType, specialization: GenericArguments, isConstructor: Bool)? {
    var entityType = resolveType(
      of: d, lookedUpIn: context, exposedTo: scopeOfUse, reportingDiagnosticsAt: name.site)
    if entityType[.hasError] { return nil }

    // TODO: Report invalid uses of mutation markers

    // The specialization of the entity includes that of the context in which it was looked up. In
    // particular, the context may contain information necessary to determine the specialization of
    // a qualified name. For example, given an instance of `type S<T> { let foo: Array<T> }`, the
    // type of the member `foo` depends on the specialization of its qualification.
    var specialization = genericQualificationArguments(inScopeIntroducing: d, resolvedIn: context)
    entityType = specialize(entityType, for: specialization, in: scopeOfUse)

    // Keep track of generic arguments that should be captured later on.
    let entityArguments = genericArguments(
      passedTo: d, typed: entityType, referredToBy: name, specializedBy: arguments,
      reportingDiagnosticsTo: &log)
    for (p, a) in entityArguments {
      specialization[p] = a
    }

    // If the match is a trait member, specialize its receiver.
    if d.kind != AssociatedTypeDecl.self,
      let t = traitDeclaring(d),
      let r = context?.type ?? resolveReceiverMetatype(in: scopeOfUse)?.instance
    {
      specialization[program[t.decl].receiver] = .type(r)
    }

    // If the name resolves to an initializer, determine if it is used as a constructor.
    let isConstructor =
      (d.kind == InitializerDecl.self) && (purpose.isConstructor || (name.value.stem == "new"))
    if isConstructor {
      entityType = ^ArrowType(constructorFormOf: ArrowType(entityType)!)
    }

    // If the receiver is an existential, replace its receiver.
    if let container = ExistentialType(context?.type) {
      entityType = entityType.asMember(of: container)
      if let t = traitDeclaring(d) {
        specialization[program[t.decl].receiver] = .type(^WitnessType(of: container))
      }
    }

    // Re-specialize the candidate's type now that the substitution map is complete contains the
    // substitutions accumulated from the candidate's qualification as well as the ones related to
    // the resolution of the candidate itself. For example, if we resolved `A<X>.f<Y>`, we'd get
    // `X` from the resolution of the qualification and `Y` from the resolution of the candidate.
    entityType = specialize(entityType, for: specialization, in: scopeOfUse)

    // If `d` is a trait requirement, we have to remember the generic arguments that are part of
    // its qualification in case its implementation is synthesized. Otherwise, we should only
    // remember arguments to parameters that are in `d`'s scope.
    var capturedArguments = GenericArguments.empty
    if program.isRequirement(d) {
      capturedArguments = specialization
    } else {
      for p in capturedGenericParameter(of: d) {
        capturedArguments[p] = specialization[p]
      }
    }

    return (entityType, capturedArguments, isConstructor)
  }

  /// Returns the generic type of a reference to `d`, found in `context`, reporting diagnostics
  /// at `diagnosticSite`.
  private mutating func resolveType(
    of d: AnyDeclID, lookedUpIn context: NameResolutionContext? = nil,
    exposedTo scopeOfUse: AnyScopeID,
    reportingDiagnosticsAt diagnosticSite: SourceRange
  ) -> AnyType {
    switch d.kind {
    case AssociatedTypeDecl.self:
      return resolveType(
        of: AssociatedTypeDecl.ID(d)!, lookedUpIn: context, exposedTo: scopeOfUse,
        reportingDiagnosticsAt: diagnosticSite)

    case SubscriptDecl.self:
      return resolveType(of: SubscriptDecl.ID(d)!, lookedUpIn: context)

    default:
      break
    }

    let result = uncheckedType(of: d)
    if let t = ParameterType(result) {
      return t.bareType
    } else {
      return result
    }
  }

  /// Returns the generic type of a reference to `d`, found in `context` and occurring in
  /// `scopeOfUse`, reporting diagnostics at `diagnosticSite`.
  private mutating func resolveType(
    of d: AssociatedTypeDecl.ID, lookedUpIn context: NameResolutionContext?,
    exposedTo scopeOfUse: AnyScopeID,
    reportingDiagnosticsAt diagnosticSite: SourceRange
  ) -> AnyType {
    if let qualification = context {
      return resolveType(
        of: d, qualifiedBy: qualification.type, exposedTo: scopeOfUse,
        reportingDiagnosticsAt: diagnosticSite)
    } else if let s = resolveTraitReceiver(in: scopeOfUse) {
      // The domain of associated type resolved without qualification is a skolem bound by the
      // trait in which the reference to `d` occurs.
      return ^MetatypeType(of: AssociatedTypeType(d, domain: ^s, ast: program.ast))
    } else {
      report(.error(invalidReferenceToAssociatedType: d, at: diagnosticSite, in: program.ast))
      return .error
    }
  }

  /// Returns the generic type of a reference to `d`, occurring qualified by `domain` in
  /// `scopeOfUse`, reporting diagnostics at `diagnosticSite`.
  private mutating func resolveType(
    of d: AssociatedTypeDecl.ID, qualifiedBy domain: AnyType,
    exposedTo scopeOfUse: AnyScopeID,
    reportingDiagnosticsAt diagnosticSite: SourceRange
  ) -> AnyType {
    // Skolems are valid associated type qualifications.
    if domain.isSkolem {
      return ^MetatypeType(of: AssociatedTypeType(d, domain: domain, ast: program.ast))
    }

    // Associated type declarations shall not be referred to outside of a generic context.
    else if domain.base is TraitType {
      report(.error(invalidReferenceToAssociatedType: d, at: diagnosticSite, in: program.ast))
      return uncheckedType(of: d)
    }

    // Type aliases used a associated type qualification are erased.
    else if let t = TypeAliasType(domain) {
      return resolveType(
        of: d, qualifiedBy: t.resolved, exposedTo: scopeOfUse,
        reportingDiagnosticsAt: diagnosticSite)
    }

    // Other qualifications refer to conformances.
    else {
      return resolveType(
        of: d, implementedBy: domain, forConformanceExposedTo: scopeOfUse,
        reportingDiagnosticsAt: diagnosticSite)
    }
  }

  /// Returns the generic type of a reference to `d`, which is implemented by `domain` for a
  /// conformance exposed to `scopeOfUse`, reporting diagnostics at `diagnosticSite`.
  ///
  /// `domain` is notionally the subject of a conformance lens focusing on its conformance to the
  /// trait that declared `d`.
  private mutating func resolveType(
    of d: AssociatedTypeDecl.ID, implementedBy domain: AnyType,
    forConformanceExposedTo scopeOfUse: AnyScopeID,
    reportingDiagnosticsAt diagnosticSite: SourceRange
  ) -> AnyType {
    let lens = traitDeclaring(d)!
    if let c = demandConformance(of: domain, to: lens, exposedTo: scopeOfUse),
      let i = c.implementations[d]?.decl
    {
      return uncheckedType(of: i)
    } else {
      report(.error(domain, doesNotConformTo: lens, at: diagnosticSite))
      return .error
    }
  }

  /// Returns the generic type of a reference to `d`, found in `context`.
  private mutating func resolveType(
    of d: SubscriptDecl.ID, lookedUpIn context: NameResolutionContext?
  ) -> AnyType {
    let result = uncheckedType(of: d)

    // Properties are not first-class.
    if let t = SubscriptType(result), t.isProperty {
      return t.output
    } else {
      return result
    }
  }

  /// Computes and returns the type of `Self` in `scopeOfUse`.
  private mutating func resolveReceiverMetatype(in scopeOfUse: AnyScopeID) -> MetatypeType? {
    switch scopeOfUse.kind {
    case ConformanceDecl.self:
      return resolveReceiverMetatype(in: ConformanceDecl.ID(scopeOfUse)!)
    case ExtensionDecl.self:
      return resolveReceiverMetatype(in: ExtensionDecl.ID(scopeOfUse)!)
    case ProductTypeDecl.self:
      return resolveReceiverMetatype(in: ProductTypeDecl.ID(scopeOfUse)!)
    case TraitDecl.self:
      return resolveReceiverMetatype(in: TraitDecl.ID(scopeOfUse)!)
    case ModuleDecl.self:
      return nil
    default:
      return resolveReceiverMetatype(in: program[scopeOfUse].scope)
    }
  }

  /// Computes and returns the type of `Self` in `scopeOfUse`.
  private mutating func resolveReceiverMetatype<T: GenericDecl>(
    in scopeOfUse: T.ID
  ) -> MetatypeType? {
    guard let unspecialized = MetatypeType(uncheckedType(of: scopeOfUse)) else {
      return nil
    }

    // Nothing more to do if the receiver isn't generic.
    guard let clause = program[scopeOfUse].genericClause else {
      return unspecialized
    }

    // Skolemize generic parameters.
    var a: BoundGenericType.Arguments = [:]
    for p in clause.value.parameters {
      a[p] = .type(^GenericTypeParameterType(p, ast: program.ast))
    }
    return MetatypeType(of: BoundGenericType(unspecialized.instance, arguments: a))
  }

  /// Computes and returns the type of `Self` in `scopeOfUse`.
  private mutating func resolveReceiverMetatype<T: TypeExtendingDecl>(
    in scopeOfUse: T.ID
  ) -> MetatypeType? {
    let t = uncheckedType(of: scopeOfUse)

    switch t.base {
    case let u as ProductType:
      return resolveReceiverMetatype(in: u.decl)
    case let u as TypeAliasType:
      return resolveReceiverMetatype(in: u.decl)
    default:
      return MetatypeType(of: t)
    }
  }

  /// Computes and returns the type of `Self` in `scopeOfUse`.
  private mutating func resolveReceiverMetatype(in scopeOfUse: TraitDecl.ID) -> MetatypeType? {
    MetatypeType(of: GenericTypeParameterType(selfParameterOf: scopeOfUse, in: program.ast))
  }

  /// Computes and returns the type of `Self` as a trait receiver in `scopeOfUse`, returning `nil`
  /// if `scopeOfUse` isn't notionally contained in a trait.
  private mutating func resolveTraitReceiver(
    in scopeOfUse: AnyScopeID
  ) -> GenericTypeParameterType? {
    resolveReceiverMetatype(in: scopeOfUse)
      .flatMap({ (t) in GenericTypeParameterType(t.instance) })
      .flatMap({ (t) in isTraitReceiver(t) ? t : nil })
  }

  /// Returns `true` if references to `d` are captured if they occur in `scopeOfUse`.
  private mutating func isCaptured(
    referenceTo d: AnyDeclID, occurringIn scopeOfUse: AnyScopeID
  ) -> Bool {
    if program.isContained(program[d].scope, in: scopeOfUse) { return false }
    if program.isGlobal(d) { return false }
    if program.isMember(d) {
      let lhs = resolveReceiverMetatype(in: program[d].scope)
      let rhs = resolveReceiverMetatype(in: program[scopeOfUse].scope)
      if lhs != rhs {
        return false
      }
    }

    // Capture-less functions are not captured.
    if d.kind == FunctionDecl.self {
      let captures = ArrowType(uncheckedType(of: d))?.environment ?? .error
      return areEquivalent(captures, .void, in: scopeOfUse)
    } else {
      return true
    }
  }

  /// Returns the generic arguments passed to `d`, which has type `t` and is being referred to by
  /// `name`, reporting diagnostics to `log`.
  private mutating func genericArguments(
    passedTo d: AnyDeclID, typed t: AnyType,
    referredToBy name: SourceRepresentable<Name>, specializedBy arguments: [CompileTimeValue],
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) -> GenericArguments {
    if let g = BoundGenericType(t) {
      assert(arguments.isEmpty, "generic declaration bound twice")
      return .init(g)
    } else {
      let p = program.ast.genericParameters(introducedBy: d)
      return associateGenericParameters(p, of: name, to: arguments, reportingDiagnosticsTo: &log)
    }
  }

  /// Returns the generic arguments passed to the qualification of symbols introduced in `d` that
  /// that have been looked up in `context`.
  ///
  /// The arguments of `context` are returned if the latter isn't `nil`. Otherwise, the arguments
  /// captured in the scope introducing `d` are returned as a table mapping accumulated generic
  /// parameters to a skolem.
  private mutating func genericQualificationArguments(
    inScopeIntroducing d: AnyDeclID, resolvedIn context: NameResolutionContext?
  ) -> GenericArguments {
    if let c = context {
      return c.arguments
    } else if d.isGenericScope {
      let parameters = accumulatedGenericParameters(in: program[d].scope)
      return .init(skolemizing: parameters, in: program.ast)
    } else {
      return .empty
    }
  }

  /// Returns a table mapping the elements of `parameters`, which are introduced by `name`'s
  /// declaration, to their corresponding values in `arguments` if the two arrays have the same
  /// length. Otherwise, returns `nil` and reports diagnostics to `log`.
  private mutating func associateGenericParameters(
    _ parameters: [GenericParameterDecl.ID], of name: SourceRepresentable<Name>,
    to arguments: [CompileTimeValue],
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) -> GenericArguments {
    var result = GenericArguments()
    for (a, p) in zip(arguments, parameters) {
      result[p] = a
    }
    for p in parameters.dropFirst(arguments.count) {
      if program[p].isTypeKinded {
        result[p] = .type(^GenericTypeParameterType(p, ast: program.ast))
      } else {
        result[p] = .term(^GenericTermParameter(p, ast: program.ast))
      }
    }

    if !arguments.isEmpty && (parameters.count != arguments.count) {
      let (f, e) = (arguments.count, parameters.count)
      log.insert(.error(invalidGenericArgumentCountTo: name, found: f, expected: e))
    }

    return result
  }

  /// Calls `action` on `self` and each constraint that must hold for a reference to `d` occurring
  /// in `scopeOfUse`.
  private mutating func forEachConstraint(
    associatedWith d: AnyDeclID, in scopeOfUse: AnyScopeID,
    do action: (inout Self, GenericConstraint) -> Void
  ) {
    switch d.kind {
    case ModuleDecl.self:
      return  // Modules have no constraints.
    case AssociatedTypeDecl.self, AssociatedValueDecl.self:
      return  // Constraints on associated types and values are assumed in their scope.
    case TraitDecl.self:
      return  // References to traits are unconstrained.
    default:
      break
    }

    if let e = possiblyPartiallyFormedEnvironment(of: d) {
      for c in e.constraints { action(&self, c) }
    }

    let lca = program.innermostCommonScope(program[d].scope, scopeOfUse)
    for s in program.scopes(from: program[d].scope) {
      if s == lca { break }
      if let g = AnyDeclID(s), let e = possiblyPartiallyFormedEnvironment(of: g) {
        for c in e.constraints { action(&self, c) }
      }
    }
  }

  /// Checks `c`, which is caused by the resolution of `n` specialized by `z` in `scopeOfUse`,
  /// reporting diagnostics to `log`.
  ///
  /// If the constraint does not contain skolems or open type variables, the result is `nil` and
  /// a diagnostic is reported to `log` iff the constraint does not hold. Otherwise, the result is
  /// a type checking constraint that has to be solved in context.
  private mutating func evaluateResolutionConstraint(
    _ c: GenericConstraint,
    associatedWith n: SourceRepresentable<Name>,
    specializedBy z: GenericArguments,
    in scopeOfUse: AnyScopeID,
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) -> Constraint? {
    switch c.value {
    case .conformance(let lhs, let rhs):
      let a = specialize(lhs, for: z, in: scopeOfUse)
      if a.isSkolem || a[.hasVariable] {
        return ConformanceConstraint(a, conformsTo: rhs, origin: .init(.binding, at: n.site))
      } else if !conforms(a, to: rhs, in: scopeOfUse) {
        log.insert(
          .error(referenceTo: n, requires: a, conformsTo: rhs, dueToConstraintAt: c.site))
      }

    case .equality(let lhs, let rhs):
      let a = specialize(lhs, for: z, in: scopeOfUse)
      let b = specialize(rhs, for: z, in: scopeOfUse)
      if a.isSkolem || a[.hasVariable] || b.isSkolem || b[.hasVariable] {
        return EqualityConstraint(a, b, origin: .init(.binding, at: n.site))
      } else if !areEquivalent(a, b, in: scopeOfUse) {
        log.insert(
          .error(referenceTo: n, requires: a, equals: rhs, dueToConstraintAt: c.site))
      }

    default:
      UNIMPLEMENTED()
    }

    return nil
  }

  /// Returns the generic parameters introduced in the generic environment of `d`.
  ///
  /// If `d` is a variant implementation, the result is the parameters introduce by the containing
  /// bundle declaration.
  private mutating func genericParameters(introducedBy d: AnyDeclID) -> [GenericParameterDecl.ID] {
    if (d.kind == MethodImpl.self) || (d.kind == SubscriptImpl.self) {
      return genericParameters(introducedBy: AnyDeclID(program[d].scope)!)
    } else if let s = program.ast[d] as? GenericScope {
      return s.genericParameters
    } else {
      return []
    }
  }

  /// Returns the generic parameters captured by `d`.
  private mutating func capturedGenericParameter<T: DeclID>(of d: T) -> [GenericParameterDecl.ID] {
    if d.kind == ModuleDecl.self {
      return []
    } else {
      var p = accumulatedGenericParameters(in: program[d].scope)
      p.append(contentsOf: program.ast.genericParameters(introducedBy: AnyDeclID(d)))
      return p
    }
  }

  /// Returns generic parameters captured by `s`.
  ///
  /// A declaration may take generic parameters even if it doesn't declare any. For example, a
  /// nested function will implicitly capture the generic parameters introduced in its context.
  mutating func accumulatedGenericParameters<T: ScopeID>(
    in s: T
  ) -> [GenericParameterDecl.ID] {
    if let r = program.scopes(from: s).first(where: \.isGenericScope) {
      return possiblyPartiallyFormedEnvironment(of: AnyDeclID(r)!)?.parameters ?? []
    } else {
      return []
    }
  }

  /// Returns the trait of which `d` is a member, or `nil` if `d` isn't member of a trait.
  mutating func traitDeclaring<T: DeclID>(_ d: T) -> TraitType? {
    guard let p = program.nodeToScope[d] else {
      assert(d.kind == ModuleDecl.self)
      return nil
    }

    switch p.kind {
    case TraitDecl.self:
      return TraitType(TraitDecl.ID(p)!, ast: program.ast)
    case ExtensionDecl.self:
      return extendedTrait(ExtensionDecl.ID(p)!)
    case MethodDecl.self:
      return traitDeclaring(MethodDecl.ID(p)!)
    case SubscriptDecl.self:
      return traitDeclaring(SubscriptDecl.ID(p)!)
    default:
      return nil
    }
  }

  /// Returns the declaration defining the value that can be passed as an implicit argument to a
  /// parameter of type `t` in scope `s`.
  mutating func implicitArgument(to t: ParameterType, exposedTo s: AnyScopeID) -> AnyDeclID? {
    for d in program[s].decls.withoutExtensions {
      if !program.isImplicitDefinition(d) { continue }

      let u = read(uncheckedType(of: d), { ParameterType($0)?.bareType ?? $0 })
      if areEquivalent(t.bareType, u, in: s) {
        return d
      }
    }

    switch s.kind {
    case FunctionDecl.self, InitializerDecl.self, MethodDecl.self, SubscriptDecl.self:
      return nil
    case ModuleDecl.self:
      preconditionFailure("implicit resolution undefined in '\(s.kind)'")
    default:
      return implicitArgument(to: t, exposedTo: program[s].scope)
    }
  }

  // MARK: Quantifier elimination

  /// A context in which a generic parameter can be instantiated.
  private struct InstantiationContext {

    /// The scope in which the parameter is being used.
    let scopeOfUse: AnyScopeID

    /// The scope extended by `scopeOfUse` if the latter is contained in an extension.
    let extendedScope: AnyScopeID?

  }

  /// Creates a context for instantiating generic parameters used in `scopeOfUse`.
  private mutating func instantiationContext(in scopeOfUse: AnyScopeID) -> InstantiationContext {
    .init(scopeOfUse: scopeOfUse, extendedScope: bridgedScope(of: scopeOfUse))
  }

  /// Creates a context for instantiating generic parameters in `scopeOfUse` by for using `r`.
  private mutating func instantiationContext(
    _ r: DeclReference, in scopeOfUse: AnyScopeID
  ) -> InstantiationContext {
    if let d = r.decl {
      return instantiationContext(forUsing: d, in: scopeOfUse)
    } else {
      return instantiationContext(in: scopeOfUse)
    }
  }

  /// Creates a context for instantiating generic parameters in `scopeOfUse` by for using `d`.
  private mutating func instantiationContext(
    forUsing d: AnyDeclID, in scopeOfUse: AnyScopeID
  ) -> InstantiationContext {
    if let i = InitializerDecl.ID(d) {
      return instantiationContext(forUsing: i, in: scopeOfUse)
    } else if isRecursive(useOf: d, in: scopeOfUse) {
      return instantiationContext(in: program[d].scope)
    } else {
      return instantiationContext(in: scopeOfUse)
    }
  }

  /// Creates a context for instantiating generic parameters in `scopeOfUse` by for using `d`.
  private mutating func instantiationContext(
    forUsing d: InitializerDecl.ID, in scopeOfUse: AnyScopeID
  ) -> InstantiationContext {
    let container = program[d].scope
    if program.isContained(scopeOfUse, in: container) {
      return instantiationContext(in: program[container].scope)
    } else {
      return instantiationContext(in: scopeOfUse)
    }
  }

  /// Replaces the generic parameters in `subject` by fresh variables, forming instantiation
  /// constraints at `site`.
  private mutating func open(type: AnyType, at site: SourceRange) -> InstantiatedType {
    // Since no generic parameter can be introduced at module scope, passing a module here will
    // force all parameters to be opened.
    instantiate(
      type, in: AnyScopeID(program.ast.coreLibrary!), cause: .init(.structural, at: site))
  }

  /// Replaces the generic parameters in `candidate` by fresh variables if their environments don't
  /// contain `scopeOfUse`, updating `substitutions` with opened generic parameters and anchoring
  /// instantiation constraints at `cause`.
  private mutating func instantiate(
    _ candidate: NameResolutionResult.Candidate, in scopeOfUse: AnyScopeID,
    updating substitutions: inout GenericArguments,
    anchoringInstantiationConstraintsAt cause: ConstraintOrigin
  ) -> NameResolutionResult.Candidate {
    let ctx = instantiationContext(candidate.reference, in: scopeOfUse)

    let t = instantiate(candidate.type, in: ctx, cause: cause, updating: &substitutions)
    var cs = candidate.constraints.union(t.constraints)

    let r = candidate.reference.modifyingArguments(mutating: &substitutions) { (s, v) in
      switch v {
      case .type(let w):
        let x = instantiate(w, in: ctx, cause: cause, updating: &s)
        cs.formUnion(x.constraints)
        return .type(x.shape)

      case .term(let w):
        return .term(instantiate(w, in: ctx, updating: &s))
      }
    }

    instantiate(
      constraints: &cs, in: ctx, updating: &substitutions,
      anchoringInstantiationConstraintsAt: cause)

    return .init(reference: r, type: t.shape, constraints: cs, diagnostics: candidate.diagnostics)
  }

  /// Replaces the generic parameters in `subject` by fresh variables if their environments don't
  /// contain `scopeOfUse`, assigning `cause` to instantiation constraints.
  private mutating func instantiate(
    _ subject: AnyType, in scopeOfUse: AnyScopeID, cause: ConstraintOrigin
  ) -> InstantiatedType {
    let ctx = instantiationContext(in: scopeOfUse)
    var substitutions = GenericArguments()
    return instantiate(subject, in: ctx, cause: cause, updating: &substitutions)
  }

  /// Replaces the generic parameters in `subject` by fresh variables if their environments don't
  /// contain `contextOfUse`, assigning `cause` to instantiation constraints.
  private mutating func instantiate(
    _ subject: AnyType, in contextOfUse: InstantiationContext, cause: ConstraintOrigin,
    updating substitutions: inout GenericArguments
  ) -> InstantiatedType {
    let shape = subject.transform(mutating: &self, transform)
    return InstantiatedType(shape: shape, constraints: [])

    func transform(mutating me: inout Self, _ t: AnyType) -> TypeTransformAction {
      // Nothing to do if `t` doesn't contain any generic parameter.
      if !t[.hasSkolem] {
        return .stepOver(t)
      }

      switch t.base {
      case let u as AssociatedTypeType:
        return transform(mutating: &me, u)
      case let u as BufferType:
        return transform(mutating: &me, u)
      case let u as GenericTypeParameterType:
        return .stepInto(me.instantiate(u, in: contextOfUse, updating: &substitutions))
      default:
        return .stepInto(t)
      }
    }

    func transform(
      mutating me: inout Self, _ t: AssociatedTypeType
    ) -> TypeTransformAction {
      let d = t.domain.transform(mutating: &me, transform)
      return .stepOver(^AssociatedTypeType(t.decl, domain: d, ast: me.program.ast))
    }

    func transform(
      mutating me: inout Self, _ t: BufferType
    ) -> TypeTransformAction {
      let n = me.instantiate(t.count, in: contextOfUse, updating: &substitutions)
      return .stepInto(^BufferType(t.element, n))
    }
  }

  /// Replaces the generic parameters in `subject` by fresh variables if their environments don't
  /// contain `contextOfUse`.
  private mutating func instantiate(
    _ subject: AnyTerm, in contextOfUse: InstantiationContext,
    updating substitutions: inout GenericArguments
  ) -> AnyTerm {
    if let p = GenericTermParameter(subject) {
      return instantiate(p, in: contextOfUse, updating: &substitutions)
    } else {
      return subject
    }
  }

  /// Returns a fresh variables if `p`' environment doesn't contain `contextOfUse`.
  private mutating func instantiate(
    _ p: GenericTypeParameterType, in contextOfUse: InstantiationContext,
    updating substitutions: inout GenericArguments
  ) -> AnyType {
    if let v = substitutions[p.decl]?.asType {
      return v
    } else {
      let v = shouldOpen(p.decl, in: contextOfUse) ? ^freshVariable() : ^p
      substitutions[p.decl] = .type(v)
      return v
    }
  }

  /// Returns a fresh variables if `p`' environment doesn't contain `contextOfUse`.
  private mutating func instantiate(
    _ p: GenericTermParameter, in contextOfUse: InstantiationContext,
    updating substitutions: inout GenericArguments
  ) -> AnyTerm {
    if let v = substitutions[p.decl]?.asTerm {
      return v
    } else {
      let v = shouldOpen(p.decl, in: contextOfUse) ? ^freshTermVariable() : ^p
      substitutions[p.decl] = .term(v)
      return v
    }
  }

  /// Instantiates the contents of `constraints` in `contextOfUse`, updating `substitutions` with
  /// opened generic parameters and anchoring instantiation constraints at `cause`.
  private mutating func instantiate(
    constraints: inout ConstraintSet, in contextOfUse: InstantiationContext,
    updating substitutions: inout GenericArguments,
    anchoringInstantiationConstraintsAt cause: ConstraintOrigin
  ) {
    var work = ConstraintSet()
    swap(&work, &constraints)

    while var c = work.popFirst() {
      c.modifyTypes { (t) in
        let x = instantiate(t, in: contextOfUse, cause: cause, updating: &substitutions)
        work.formUnion(x.constraints)
        return x.shape
      }
      constraints.insert(c)
    }
  }

  /// Returns `true` iff `contextOfUse` is not contained in `p`'s environment.
  private func shouldOpen(
    _ p: GenericParameterDecl.ID, in contextOfUse: InstantiationContext
  ) -> Bool {
    // Generic parameters introduced by a trait can't be referenced outside of their environment.
    let introductionScope = program[p].scope
    if introductionScope.kind == TraitDecl.self {
      return false
    }

    // Reference is contained if it's lexically enclosed in the parameter's environment or if it
    // occurs in an extension of the scope associated with that environment.
    if program.isContained(contextOfUse.scopeOfUse, in: introductionScope) {
      return false
    } else if let s = contextOfUse.extendedScope {
      return !program.isContained(s, in: introductionScope)
    }

    // Reference is not contained.
    return true
  }

  /// Returns `true` iff a use of `d` in `scopeOfUse` is recursive.
  private func isRecursive(useOf d: AnyDeclID, in scopeOfUse: AnyScopeID) -> Bool {
    if let s = AnyScopeID(d) {
      return d.isCallable && program.isContained(scopeOfUse, in: s)
    } else {
      return false
    }
  }

  // MARK: Type inference

  /// Returns the inferred type of `d`, which is is used as `purpose`, inserting new proof
  /// obligations in `obligations`.
  private mutating func inferredType(
    of d: BindingDecl.ID, usedAs purpose: BindingDeclUse,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let p = program[d].pattern
    let lhs = inferredType(of: p.id, withHint: purpose.filteredType, updating: &obligations)
    if lhs[.hasError] { return lhs }

    // If `d` has no initializer, its type is that of its annotation, if present. Otherwise, its
    // pattern must be used as a filter and `d` is inferred to have the same type.
    guard let i = program[d].initializer else {
      switch purpose {
      case .irrefutable:
        assert(p.annotation != nil, "expected type annotation")
        if !p.introducer.value.isConsuming && program.isLocal(d) {
          report(.error(binding: p.introducer.value, requiresInitializerAt: p.introducer.site))
          return .error
        } else {
          return lhs
        }

      case .condition:
        assert(p.annotation != nil, "expected type annotation")
        return lhs

      case .filter:
        return lhs
      }
    }

    // Note: `i` should not have been assigned a type if before `d` is checked.
    assert(cache.local.exprType[i] == nil)
    let rhs = constrain(i, to: ^freshVariable(), in: &obligations)

    // If `p` is an option pattern, the initializer must be an option of the pattern's type.
    // E.g. `if let x? = y { ... }`
    if let q = OptionPattern.ID(p.subpattern.id) {
      if purpose == .irrefutable {
        report(.error(invalidOptionPattern: q, in: program.ast))
        return .error
      } else {
        let u = program.ast.optional(lhs)
        let o = ConstraintOrigin(.optionalBinding, at: program[i].site)
        obligations.insert(EqualityConstraint(^u, rhs, origin: o))
      }
    }

    // If `d` has no annotation, its type is inferred as that of its initializer.
    // E.g. `let x = 42`
    else if p.annotation == nil {
      let o = ConstraintOrigin(.initializationWithPattern, at: program[i].site)
      obligations.insert(EqualityConstraint(rhs, lhs, origin: o))
    }

    // If `d` is used irrefutably, the initializer's type must be subtype of the pattern's.
    // E.g. `let x: Int = 42`
    else if purpose == .irrefutable {
      let o = ConstraintOrigin(.initializationWithHint, at: program[i].site)
      obligations.insert(SubtypingConstraint(rhs, lhs, origin: o))
    }

    // If `d` is used as a condition, the initializer's type must be supertype of the pattern's.
    // E.g. `if let x: Int = y { ... }`
    else {
      let o = ConstraintOrigin(.optionalBinding, at: program[i].site)
      obligations.insert(SubtypingConstraint(lhs, rhs, origin: o))
    }

    // Collect the proof obligations for the initializer. The resulting type can be discarded; the
    // type of `i` will be assigned after the all proof obligations are discharged.
    _ = inferredType(of: i, withHint: lhs, updating: &obligations)
    return lhs
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType<T: ExprID>(
    of e: T, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // Preserve choices already committed to the AST.
    if let t = cache.local.exprType[e] { return t }
    defer { assert(obligations.exprType[e] != nil) }

    switch e.kind {
    case ArrowTypeExpr.self:
      return _inferredType(of: ArrowTypeExpr.ID(e)!, withHint: hint, updating: &obligations)
    case BooleanLiteralExpr.self:
      return _inferredType(of: BooleanLiteralExpr.ID(e)!, withHint: hint, updating: &obligations)
    case BufferLiteralExpr.self:
      return _inferredType(of: BufferLiteralExpr.ID(e)!, withHint: hint, updating: &obligations)
    case CaptureExpr.self:
      return _inferredType(of: CaptureExpr.ID(e)!, withHint: hint, updating: &obligations)
    case CastExpr.self:
      return _inferredType(of: CastExpr.ID(e)!, withHint: hint, updating: &obligations)
    case ConditionalExpr.self:
      return _inferredType(of: ConditionalExpr.ID(e)!, withHint: hint, updating: &obligations)
    case ConformanceLensExpr.self:
      return _inferredType(of: ConformanceLensExpr.ID(e)!, withHint: hint, updating: &obligations)
    case ExistentialTypeExpr.self:
      return _inferredType(of: ExistentialTypeExpr.ID(e)!, withHint: hint, updating: &obligations)
    case FloatLiteralExpr.self:
      return _inferredType(of: FloatLiteralExpr.ID(e)!, withHint: hint, updating: &obligations)
    case FunctionCallExpr.self:
      return _inferredType(of: FunctionCallExpr.ID(e)!, withHint: hint, updating: &obligations)
    case InoutExpr.self:
      return _inferredType(of: InoutExpr.ID(e)!, withHint: hint, updating: &obligations)
    case IntegerLiteralExpr.self:
      return _inferredType(of: IntegerLiteralExpr.ID(e)!, withHint: hint, updating: &obligations)
    case LambdaExpr.self:
      return _inferredType(of: LambdaExpr.ID(e)!, withHint: hint, updating: &obligations)
    case MatchExpr.self:
      return _inferredType(of: MatchExpr.ID(e)!, withHint: hint, updating: &obligations)
    case NameExpr.self:
      return _inferredType(of: NameExpr.ID(e)!, withHint: hint, updating: &obligations)
    case PragmaLiteralExpr.self:
      return _inferredType(of: PragmaLiteralExpr.ID(e)!, withHint: hint, updating: &obligations)
    case RemoteTypeExpr.self:
      return _inferredType(of: RemoteTypeExpr.ID(e)!, withHint: hint, updating: &obligations)
    case SequenceExpr.self:
      return _inferredType(of: SequenceExpr.ID(e)!, withHint: hint, updating: &obligations)
    case StringLiteralExpr.self:
      return _inferredType(of: StringLiteralExpr.ID(e)!, withHint: hint, updating: &obligations)
    case SubscriptCallExpr.self:
      return _inferredType(of: SubscriptCallExpr.ID(e)!, withHint: hint, updating: &obligations)
    case TupleExpr.self:
      return _inferredType(of: TupleExpr.ID(e)!, withHint: hint, updating: &obligations)
    case TupleMemberExpr.self:
      return _inferredType(of: TupleMemberExpr.ID(e)!, withHint: hint, updating: &obligations)
    case TupleTypeExpr.self:
      return _inferredType(of: TupleTypeExpr.ID(e)!, withHint: hint, updating: &obligations)
    case WildcardExpr.self:
      return _inferredType(of: WildcardExpr.ID(e)!, withHint: hint, updating: &obligations)
    default:
      unexpected(e, in: program.ast)
    }
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: ArrowTypeExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let environment: AnyType
    if let v = program[e].environment {
      environment = evalPartialTypeAnnotation(v, updating: &obligations) ?? .error
    } else {
      environment = .any
    }

    let inputs = evalParameterAnnotations(of: e)
    let output = evalTypeAnnotation(program[e].output)

    let r = ^ArrowType(
      receiverEffect: program[e].receiverEffect?.value ?? .let,
      environment: environment,
      inputs: inputs,
      output: output)
    return constrain(e, to: ^MetatypeType(of: r), in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: BooleanLiteralExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    constrain(e, to: ^program.ast.coreType("Bool")!, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: BufferLiteralExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let elementHint: AnyType
    if let h = hint, let b = BufferType(canonical(h, in: program[e].scope)) {
      elementHint = b.element
    } else {
      elementHint = ^freshVariable()
    }

    // If the buffer has no element, we keep the element type open. Otherwise, we use the type of
    // the first element to constrain all others.
    if let elements = program[e].elements.headAndTail {
      let head = inferredType(of: elements.head, withHint: elementHint, updating: &obligations)
      for x in elements.tail {
        let t = inferredType(of: x, withHint: head, updating: &obligations)
        if !areEquivalent(t, head, in: program[e].scope) {
          let o = ConstraintOrigin(.structural, at: program[x].site)
          obligations.insert(EqualityConstraint(head, t, origin: o))
        }
      }

      let n = ConcreteTerm(wrapping: program[e].elements.count)
      return constrain(e, to: ^BufferType(head, ^n), in: &obligations)
    } else {
      let n = ConcreteTerm(wrapping: 0)
      return constrain(e, to: ^BufferType(elementHint, ^n), in: &obligations)
    }
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: CaptureExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let t = inferredType(
      of: program[e].source, withHint: RemoteType(hint)?.bareType, updating: &obligations)
    return constrain(e, to: ^RemoteType(program[e].access.value, t), in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: CastExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    guard let target = evalPartialTypeAnnotation(program[e].right, updating: &obligations) else {
      return constrain(e, to: .error, in: &obligations)
    }

    let cause = ConstraintOrigin(.cast, at: program[e].site)
    let rhs = instantiate(target, in: program[e].scope, cause: cause)
    obligations.insert(rhs.constraints)

    switch program[e].direction {
    case .down:
      // Note: constraining the type of the LHS to be above the RHS wouldn't contribute any useful
      // information to the constraint system.
      _ = inferredType(of: program[e].left, updating: &obligations)
      return constrain(e, to: rhs.shape, in: &obligations)

    case .up:
      // The type of the LHS must be statically known to subtype of the RHS.
      let lhs = inferredType(
        of: program[e].left, withHint: ^freshVariable(), updating: &obligations)
      obligations.insert(SubtypingConstraint(lhs, rhs.shape, origin: cause))
      return constrain(e, to: rhs.shape, in: &obligations)

    case .pointerConversion:
      // The LHS be a `Builtin.ptr`. The RHS must be a remote type.
      guard let s = RemoteType(rhs.shape) else {
        report(.error(invalidPointerConversionAt: program[e].right.site))
        return constrain(e, to: .error, in: &obligations)
      }

      let lhs = inferredType(of: program[e].left, updating: &obligations)
      obligations.insert(EqualityConstraint(lhs, .builtin(.ptr), origin: cause))
      return constrain(e, to: s.bareType, in: &obligations)
    }
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: ConditionalExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // Condition doesn't participate in inference.
    check(program[e].condition)

    let a = inferredType(of: program[e].success, withHint: hint, updating: &obligations)
    let b = inferredType(of: program[e].failure.value, withHint: hint, updating: &obligations)
    let t = ^freshVariable()
    obligations.insert(
      MergingConstraint(t, [a, b], origin: .init(.branchMerge, at: program[e].introducerSite)))
    return constrain(e, to: t, in: &obligations)
  }

  private mutating func _inferredType(
    of e: ConformanceLensExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    guard
      let t = evalPartialTypeAnnotation(program[e].lens, updating: &obligations),
      let s = evalPartialTypeAnnotation(program[e].subject, updating: &obligations)
    else {
      return constrain(e, to: .error, in: &obligations)
    }

    guard let lens = TraitType(t) else {
      report(.error(notATrait: t, at: program[e].lens.site))
      return constrain(e, to: .error, in: &obligations)
    }

    guard conforms(s, to: lens, in: program[e].scope) else {
      report(.error(s, doesNotConformTo: lens, at: program[e].lens.site))
      return constrain(e, to: .error, in: &obligations)
    }

    // DR: It seems fishy that we don't have to return a metatype.
    let r = ConformanceLensType(viewing: s, through: lens)
    return constrain(e, to: ^r, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: ExistentialTypeExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let (i, cs) = eval(existentialInterface: program[e].traits)

    guard cs.isEmpty else { UNIMPLEMENTED() }
    guard program[e].whereClause == nil else { UNIMPLEMENTED() }

    let r = ExistentialType(i, constraints: cs)
    return constrain(e, to: ^MetatypeType(of: r), in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: FloatLiteralExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let t = ^program.ast.coreType("Float64")!
    return _inferredType(ofLiteral: e, withHint: hint, defaultingTo: t, updating: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: FunctionCallExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // We need the type of the callee to infer anything further.
    let callee = inferredCalleeType(of: e, implicitlyIn: hint, updating: &obligations)
    if callee.isError {
      return constrain(e, to: .error, in: &obligations)
    }

    // The callee has a callable type or we need inference to determine its type. Either way,
    // constraint the callee and its arguments with a function call constraints.
    if isArrow(callee) || (callee.base is TypeVariable) {
      return _inferredType(of: e, withCallee: callee, withHint: hint, updating: &obligations)
    }

    // In any other case, the callee is known to be not callable.
    report(.error(cannotCall: callee, as: .function, at: program[e].callee.site))
    return constrain(e, to: .error, in: &obligations)
  }

  /// Returns the inferred type of `e` knowing its callee has type `callee`, updating `obligations`
  /// and gathering contextual information from `hint`.
  private mutating func _inferredType(
    of e: FunctionCallExpr.ID, withCallee callee: AnyType, withHint hint: AnyType?,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    var arguments: [CallConstraint.Argument] = []
    for a in program[e].arguments {
      let p = inferredType(of: a.value, withHint: ^freshVariable(), updating: &obligations)
      arguments.append(.init(label: a.label, type: p, valueSite: program[a.value].site))
    }

    let isMutating = program.ast.isMarkedForMutation(program[e].callee)
    let output =
      (callee.base as? CallableType)?.outputOfUse(mutable: isMutating)
      ?? hint
      ?? ^freshVariable()

    obligations.insert(
      CallConstraint(
        arrow: callee, usedMutably: isMutating,
        takes: arguments, gives: output, in: .ast(AnyExprID(e)),
        origin: .init(.callee, at: program[e].callee.site)))

    return constrain(e, to: output, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: InoutExpr.ID, usedAs purpose: NameUse = .unapplied, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let t = inferredType(of: program[e].subject, withHint: hint, updating: &obligations)
    return constrain(e, to: t, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: IntegerLiteralExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let t = ^program.ast.coreType("Int")!
    return _inferredType(ofLiteral: e, withHint: hint, defaultingTo: t, updating: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: LambdaExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let h = ArrowType(hint)
    let d = program[e].decl.id
    let inputs = uncheckedInputTypes(of: e, withHint: h)

    let captures = uncheckedCaptureTypes(of: d)
    let environment = TupleType(captures.explicit + captures.implicit)

    let output = inferredReturnType(of: e, withHint: h?.output, updating: &obligations)
    if output.isError {
      return constrain(e, to: .error, in: &obligations)
    }

    let effect: AccessEffect
    if let k = program[d].receiverEffect {
      effect = k.value
    } else if program[d].explicitCaptures.contains(where: isVar(_:)) {
      effect = .inout
    } else if captures.implicit.contains(where: { RemoteType($0.type)!.access == .inout }) {
      effect = .inout
    } else {
      effect = .let
    }

    let result = ^ArrowType(
      receiverEffect: effect,
      environment: ^environment,
      inputs: inputs, output: output)
    obligations.assign(result, to: AnyDeclID(d))
    return constrain(e, to: result, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: MatchExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let subject = inferredType(of: program[e].subject, updating: &obligations)
    for c in program[e].cases {
      _ = inferredType(of: program[c].pattern, withHint: subject, updating: &obligations)
    }
    return constrain(e, to: AnyType.void, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint` and `implicitQualification`.
  ///
  /// If the leftmost component of `e` is implicit, (e.g., `.foo.bar`), then its next component is
  /// resolved using qualified name lookup in `implicitQualification`. `purpose` describes the way
  /// `e` is used.
  private mutating func _inferredType(
    of e: NameExpr.ID,
    implicitlyIn implicitQualification: AnyType? = nil,
    usedAs purpose: NameUse = .unapplied,
    withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let resolution = resolve(e, usedAs: purpose) { (me, n) in
      me.inferredQualification(of: n, implicitlyIn: implicitQualification, updating: &obligations)
    }

    let unresolved: [NameExpr.ID]
    var lastVisited: AnyType?

    switch resolution {
    case .failed:
      return constrain(e, to: .error, in: &obligations)

    case .canceled(let p, let suffix):
      if p == nil {
        report(.error(noContextToResolve: program[e].name.value, at: program[e].name.site))
        return constrain(e, to: .error, in: &obligations)
      }
      unresolved = suffix
      lastVisited = p

    case .done(let prefix, let suffix):
      unresolved = suffix
      lastVisited = constrain(prefix, in: &obligations)
    }

    // Create the necessary constraints to let the solver resolve the remaining components.
    for i in (0..<unresolved.count).reversed() {
      let memberType = ^freshVariable()
      obligations.insert(
        MemberConstraint(
          lastVisited!, hasMember: memberType, referredToBy: unresolved[i], in: program.ast,
          usedAs: (i == 0) ? purpose : .unapplied,
          origin: ConstraintOrigin(.member, at: program[unresolved[i]].site)))
      lastVisited = constrain(unresolved[i], to: memberType, in: &obligations)
    }

    return lastVisited!
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: PragmaLiteralExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    switch program.ast[e].kind {
    case .file:
      return constrain(e, to: ^program.ast.coreType("String")!, in: &obligations)
    case .line:
      return constrain(e, to: ^program.ast.coreType("Int")!, in: &obligations)
    }
  }

  /// Returns the inferred type of `e`, using `hint` for context and updating `obligations`.
  private mutating func _inferredType(
    of e: RemoteTypeExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let t = evalTypeAnnotation(program[e].operand)
    let r = RemoteType(program[e].convention.value, t)
    return constrain(e, to: ^MetatypeType(of: r), in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: SequenceExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // Transform the sequence into a binary tree.
    guard let tree = fold(e) else {
      return constrain(e, to: .error, in: &obligations)
    }

    // Generate constraints from the folded sequence.
    let root = _inferredType(of: tree, withHint: hint, updating: &obligations)
    return constrain(e, to: root, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: FoldedSequenceExpr, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    switch e {
    case .infix(let callee, let lhs, let rhs):
      // Infer the types of the operands.
      let lhsType = _inferredType(of: lhs, updating: &obligations)
      let rhsType = _inferredType(of: rhs, withHint: ^freshVariable(), updating: &obligations)

      if lhsType.isError || rhsType.isError {
        return .error
      }

      let operatorType = ^freshVariable()
      let outputType = ^freshVariable()
      constrain(callee.expr, to: operatorType, in: &obligations)

      // The operator is a member function of the left operand.
      obligations.insert(
        MemberConstraint(
          lhsType, hasMember: operatorType, referredToBy: callee.expr, in: program.ast,
          usedAs: .unapplied,
          origin: .init(.member, at: program[callee.expr].site)))
      obligations.insert(
        CallConstraint(
          arrow: operatorType,
          usedMutably: program.ast.isMarkedForMutation(lhs),
          takes: [.init(label: nil, type: rhsType, valueSite: program.ast.site(of: rhs))],
          gives: outputType,
          in: .infix(e),
          origin: .init(.callee, at: program.ast.site(of: e))))

      return outputType

    case .leaf(let l):
      return inferredType(of: l, withHint: hint, updating: &obligations)
    }
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: StringLiteralExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    constrain(e, to: ^program.ast.coreType("String")!, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: SubscriptCallExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // We need the type of the callee to infer anything further.
    let callee = inferredCalleeType(of: e, implicitlyIn: hint, updating: &obligations)
    if callee.isError {
      return constrain(e, to: .error, in: &obligations)
    }

    // The callee has a metatype and is a name expression bound to a nominal type declaration,
    // meaning that the call is actually a sugared array or buffer type expression.
    if isBoundToNominalTypeDecl(program[e].callee, in: obligations) {
      let t = MetatypeType(callee)!.instance
      switch program[e].arguments.count {
      case 0:
        let u = MetatypeType(of: program.ast.array(t))
        return constrain(e, to: ^u, in: &obligations)
      case 1:
        let u = evalBufferTypeExpression(e, havingInferredElementType: t)
        return constrain(e, to: ^u, in: &obligations)
      case let n:
        report(.error(invalidBufferTypeArgumentCount: n, at: program[e].callee.site))
        return constrain(e, to: .error, in: &obligations)
      }
    }

    // The callee has a callable type or we need inference to determine its type. Either way,
    // constraint the callee and its arguments with a function call constraints.
    if isSubscript(callee) || (callee.base is TypeVariable) {
      return _inferredType(of: e, withCallee: callee, withHint: hint, updating: &obligations)
    }

    // In any other case, the callee is known to be not callable.
    report(.error(cannotCall: callee, as: .subscript, at: program[e].callee.site))
    return constrain(e, to: .error, in: &obligations)
  }

  /// Returns the inferred type of `e` knowing its callee has type `callee`, updating `obligations`
  /// and gathering contextual information from `hint`.
  private mutating func _inferredType(
    of e: SubscriptCallExpr.ID, withCallee callee: AnyType, withHint hint: AnyType?,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    var arguments: [CallConstraint.Argument] = []
    for a in program[e].arguments {
      let p = inferredType(of: a.value, withHint: ^freshVariable(), updating: &obligations)
      arguments.append(.init(label: a.label, type: p, valueSite: program[a.value].site))
    }

    let isMutating = program.ast.isMarkedForMutation(program[e].callee)
    let output =
      (callee.base as? CallableType)?.outputOfUse(mutable: isMutating)
      ?? hint
      ?? ^freshVariable()

    obligations.insert(
      CallConstraint(
        subscript: callee, usedMutably: program.ast.isMarkedForMutation(program[e].callee),
        takes: arguments, gives: output, in: .ast(AnyExprID(e)),
        origin: .init(.callee, at: program[e].callee.site)))

    return constrain(e, to: output, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: TupleExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let elements = program[e].elements
    var elementTypes: [TupleType.Element] = []

    // If the expected type is a tuple compatible with the shape of the expression, propagate that
    // information down the expression tree. Otherwise, infer the type of the expression from the
    // leaves and use type constraints to detect potential mismatch.
    if let type = TupleType(hint),
      type.elements.elementsEqual(elements, by: { (a, b) in a.label == b.label?.value })
    {
      for (t, e) in zip(type.elements, elements) {
        let u = inferredType(of: e.value, withHint: t.type, updating: &obligations)
        elementTypes.append(.init(label: e.label?.value, type: u))
      }
    } else {
      for e in elements {
        let u = inferredType(of: e.value, withHint: nil, updating: &obligations)
        elementTypes.append(.init(label: e.label?.value, type: u))
      }
    }

    return constrain(e, to: ^TupleType(elementTypes), in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: TupleMemberExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let s = inferredType(of: program[e].tuple, withHint: nil, updating: &obligations)
    let t = ^freshVariable()
    let i = program[e].index
    obligations.insert(
      TupleMemberConstraint(s, at: i.value, hasType: t, origin: .init(.member, at: i.site)))
    return constrain(e, to: t, in: &obligations)
  }

  /// Returns the inferred type of `e`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func _inferredType(
    of e: TupleTypeExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    var elementTypes: [TupleType.Element] = []
    for e in program[e].elements {
      let t = evalPartialTypeAnnotation(e.type, updating: &obligations) ?? .error
      elementTypes.append(.init(label: e.label?.value, type: t))
    }

    let r = TupleType(elementTypes)
    return constrain(e, to: ^MetatypeType(of: r), in: &obligations)
  }

  /// Returns the inferred type of `e` using `hint` for context and updating `obligations`.
  private mutating func _inferredType(
    of e: WildcardExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let r = hint ?? ^freshVariable()
    return constrain(e, to: ^MetatypeType(of: r), in: &obligations)
  }

  /// Returns the inferred type of `e`'s callee using `q` to resolve implicit qualifications and
  /// updating `obligations`.
  private mutating func inferredCalleeType(
    of e: FunctionCallExpr.ID, implicitlyIn q: AnyType?,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let c = program[e].callee.id
    let p = NameUse.function(
      labels: program[e].arguments.map(\.label?.value), mutating: c.kind == InoutExpr.self)
    return inferredType(ofCallee: c, usedAs: p, implicitlyIn: q, updating: &obligations)
  }

  /// Returns the inferred type of `e`'s callee using `q` to resolve implicit qualifications and
  /// updating `obligations`.
  private mutating func inferredCalleeType(
    of e: SubscriptCallExpr.ID, implicitlyIn q: AnyType?,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    let c = program[e].callee.id
    let p = NameUse.subscript(
      labels: program[e].arguments.map(\.label?.value))
    return inferredType(ofCallee: c, usedAs: p, implicitlyIn: q, updating: &obligations)
  }

  /// Returns the inferred type of `callee`, which is a callee used as `purpose`, using `q` to
  /// resolve implicit qualifications and updating `obligations`.
  private mutating func inferredType(
    ofCallee callee: AnyExprID, usedAs purpose: NameUse, implicitlyIn q: AnyType?,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    switch callee.kind {
    case InoutExpr.self:
      let e = program[InoutExpr.ID(callee)!].subject.id
      let t = inferredType(ofCallee: e, usedAs: purpose, implicitlyIn: q, updating: &obligations)
      return constrain(callee, to: t, in: &obligations)

    case NameExpr.self:
      let e = NameExpr.ID(callee)!
      return _inferredType(of: e, implicitlyIn: q, usedAs: purpose, updating: &obligations)

    default:
      return inferredType(of: callee, updating: &obligations)
    }
  }

  /// Returns the inferred type of `literal`, which is a literal, updating `obligations`, gathering
  /// contextual information from `hint`, and defaulting to `defaultType` if contextual information
  /// doesn't allow top-down inference.
  ///
  /// If `hint` is not `nil`, it is constrained to be conforming to the `ExpressibleBy***Literal`
  /// corresponding to `defaultType` and the type of `e` if inferred as `hint`. Otherwise, the
  /// type of `literal` is inferred as `defaultType`.
  ///
  /// - Requires: `literal` is a literal expression.
  private mutating func _inferredType<T: Expr>(
    ofLiteral literal: T.ID, withHint hint: AnyType? = nil, defaultingTo defaultType: AnyType,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // Use the default type in the absence of any hint.
    guard let h = hint else {
      return constrain(literal, to: defaultType, in: &obligations)
    }

    // Trivial if `h` is the default type.
    if areEquivalent(defaultType, h, in: program[literal].scope) {
      return constrain(literal, to: h, in: &obligations)
    }

    // Trivial if `h` conforms to `ExpressibleBy***Literal`.
    let p = program.ast.coreTrait(forTypesExpressibleBy: T.self)!
    if conforms(h, to: p, in: program[literal].scope) {
      return constrain(literal, to: h, in: &obligations)
    }

    // Trivial if `h` provably doesn't conform to `ExpressibleBy***Literal`.
    if !h[.hasVariable] {
      report(.error(h, doesNotConformTo: p, at: program[literal].site))
      return .error
    }

    // In other cases, we infer a type conforming to `ExpressibleBy***Literal`, preferring the
    // default type if the hint doesn't give us any better information.
    let cause = ConstraintOrigin(.literal, at: program[literal].site)
    let a: ConstraintSet = [EqualityConstraint(defaultType, h, origin: cause)]
    let b: ConstraintSet = [ConformanceConstraint(h, conformsTo: p, origin: cause)]
    obligations.insert(
      DisjunctionConstraint(
        between: [.init(constraints: a, penalties: 0), .init(constraints: b, penalties: 1)],
        origin: cause))

    // return constrain(literal, to: t, in: &obligations)
    return constrain(literal, to: h, in: &obligations)
  }

  /// Returns the inferred type of `e`'s output, updating `obligations` and gathering contextual
  /// information from `hint`.
  private mutating func inferredReturnType(
    of e: LambdaExpr.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    if let o = program[e].decl.output {
      return evalTypeAnnotation(o)
    } else if case .expr(let b) = program[e].decl.body {
      return inferredType(of: b, withHint: hint, updating: &obligations)
    } else {
      report(.error(cannotInferComplexReturnTypeAt: program[e].decl.introducerSite))
      return .error
    }
  }

  /// Returns the inferred type of `p`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType(
    of p: AnyPatternID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    switch p.kind {
    case BindingPattern.self:
      return inferredType(of: BindingPattern.ID(p)!, withHint: hint, updating: &obligations)
    case ExprPattern.self:
      return inferredType(of: ExprPattern.ID(p)!, withHint: hint, updating: &obligations)
    case NamePattern.self:
      return inferredType(of: NamePattern.ID(p)!, withHint: hint, updating: &obligations)
    case OptionPattern.self:
      return inferredType(of: OptionPattern.ID(p)!, withHint: hint, updating: &obligations)
    case TuplePattern.self:
      return inferredType(of: TuplePattern.ID(p)!, withHint: hint, updating: &obligations)
    case WildcardPattern.self:
      return inferredType(of: WildcardPattern.ID(p)!, withHint: hint, updating: &obligations)
    default:
      unexpected(p, in: program.ast)
    }
  }

  /// Returns the inferred type of `p`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType(
    of p: BindingPattern.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // A binding pattern introduces additional type information when it has a type annotation. In
    // that case, the type denoted by the annotation is used to infer the type of the sub-pattern
    // and constrained to be a subtype of the expected type, if any.
    let subpattern: AnyType?
    if let a = program[p].annotation {
      if let t = evalPartialTypeAnnotation(a, withHint: hint, updating: &obligations) {
        subpattern = t
      } else {
        subpattern = .error
      }
    } else {
      subpattern = hint
    }

    return inferredType(of: program[p].subpattern, withHint: subpattern, updating: &obligations)
  }

  /// Returns the inferred type of `p`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType(
    of p: ExprPattern.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    inferredType(of: program[p].expr, withHint: hint, updating: &obligations)
  }

  /// Returns the inferred type of `p`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType(
    of p: NamePattern.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // Note: `declType` is set only if we're visiting the containing pattern more than once.
    let t = cache.local.declType[program[p].decl] ?? hint ?? ^freshVariable()
    obligations.assign(t, to: AnyDeclID(program[p].decl))
    return t
  }

  /// Returns the inferred type of `p`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType(
    of p: OptionPattern.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    inferredType(of: program[p].name, updating: &obligations)
  }

  /// Returns the inferred type of `p`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType(
    of p: TuplePattern.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    // Infer the shape of the expected type if we don't a context.
    guard let h = hint else {
      return ^TupleType(
        program[p].elements.map { (a) in
          let t = inferredType(of: a.pattern, updating: &obligations)
          return .init(label: a.label?.value, type: t)
        })
    }

    // If we have a context, it must be a tuple or a variable.
    if let t = TupleType(h) {
      if t.elements.count != program[p].elements.count {
        return skip(.error(invalidDestructuringOfType: h, at: program[p].site))
      }

      var lhs: [String?] = []
      var rhs: [String?] = []

      // Visit the elements pairwise.
      for (a, b) in zip(program[p].elements, t.elements) {
        let t = inferredType(of: a.pattern, withHint: b.type, updating: &obligations)
        if t.isError { return .error }
        lhs.append(a.label?.value)
        rhs.append(b.label)
      }

      // Check that labels match.
      if lhs != rhs {
        report(.error(labels: lhs, incompatibleWith: rhs, at: program[p].site))
        return .error
      }
    } else if !(h.base is TypeVariable) {
      return skip(.error(invalidDestructuringOfType: h, at: program[p].site))
    }

    return h

    /// Reports `d`, assigns all declarations in `p` to `.error`, and returns `.error`.
    func skip(_ d: Diagnostic) -> AnyType {
      for (_, n) in program.ast.names(in: p) {
        let t = cache.local.declType[program[n].decl] ?? .error
        obligations.assign(t, to: AnyDeclID(program[n].decl))
      }
      report(d)
      return .error
    }
  }

  /// Returns the inferred type of `p`, updating `obligations` and gathering contextual information
  /// from `hint`.
  private mutating func inferredType(
    of p: WildcardPattern.ID, withHint hint: AnyType? = nil,
    updating obligations: inout ProofObligations
  ) -> AnyType {
    hint ?? ^freshVariable()
  }

  /// Returns the inferred type of the elements over which `s` iterates.
  ///
  /// The returned type is obtained by looking at the traits implemented by the type `D` of the
  /// loop's iteration domain. For a non-consuming loop (i.e., a loop whose pattern is introduced
  /// with `let` or `inout`), the return value is the implementation of `Collection.Element` for
  /// `D`'s conformance to `Collection` in the innermost scope enclosing `s`. If such a conformance
  /// does not exist, or if the loop is consuming, then the return value is the implementation of
  /// `Iterator.Element` for `D`'s conformance to `Iterator`, or `nil` if such a conformance doesn
  /// not exist.
  private mutating func inferredIterationElementType(of s: ForStmt.ID) -> AnyType? {
    guard let domain = checkedType(of: program[s].domain.value).errorFree else { return nil }

    let isConsuming = program.ast.isConsuming(s)
    let collection = program.ast.core.collection.type
    let iterator = program.ast.core.iterator.type

    // By default, non-consuming loops use `Collection`.
    if !isConsuming && conforms(domain, to: collection, in: program[s].scope) {
      let r = AssociatedTypeDecl.ID(program.ast.requirements("Element", in: collection.decl)[0])!
      return demandImplementation(of: r, for: domain, in: program[s].scope)
    }

    // Any kind of for loop can consume an iterator.
    if conforms(domain, to: iterator, in: program[s].scope) {
      let r = AssociatedTypeDecl.ID(program.ast.requirements("Element", in: iterator.decl)[0])!
      return demandImplementation(of: r, for: domain, in: program[s].scope)
    }

    let d = Diagnostic.error(
      invalidForLoopDomain: domain,
      consuming: isConsuming,
      at: program[program[s].domain.value].site)
    report(d)
    return nil
  }

  /// Updates `obligations` with the constraints implied by the result of name resolution for each
  /// element in `components`.
  private mutating func constrain(
    _ components: [NameResolutionResult.ResolvedComponent], in obligations: inout ProofObligations
  ) -> AnyType {
    var last: AnyType?
    var substitutions = GenericArguments()
    for p in components {
      last = constrain(p.component, to: p.candidates, in: &obligations, extending: &substitutions)
    }
    return last!
  }

  /// Updates `obligations` to constrain `name` as a reference to one of `candidates`, extending
  /// `substitutions` with opened generic parameters, and returning the inferred type of `name`.
  ///
  /// - Requires: `candidates` is not empty
  private mutating func constrain(
    _ name: NameExpr.ID, to candidates: [NameResolutionResult.Candidate],
    in obligations: inout ProofObligations,
    extending substitutions: inout GenericArguments
  ) -> AnyType {
    precondition(!candidates.isEmpty)
    let site = program[name].site

    // If there's only one candidate, commit to this choice.
    if var pick = candidates.uniqueElement {
      pick = instantiate(
        pick, in: program[name].scope,
        updating: &substitutions,
        anchoringInstantiationConstraintsAt: .init(.binding, at: site))
      obligations.assign(pick.reference, to: name)
      obligations.insert(pick.constraints)
      return constrain(name, to: pick.type, in: &obligations)
    }

    // Otherwise, create an overload set.
    let overloads: [OverloadConstraint.Predicate] = candidates.map({ (candidate) in
      let penalties = candidate.reference.decl.map({ program.isRequirement($0) ? 1 : 0 }) ?? 0
      let pick = instantiate(
        candidate, in: program[name].scope,
        updating: &substitutions,
        anchoringInstantiationConstraintsAt: .init(.binding, at: site))
      return .init(pick, penalties: penalties)
    })

    // Constrain the name to refer to one of the overloads.
    let t = ^freshVariable()
    let overload = OverloadConstraint(
      name, withType: t, refersToOneOf: overloads, origin: .init(.binding, at: site))
    obligations.insert(overload)
    return constrain(name, to: t, in: &obligations)
  }

  /// Constrains `subject` to have type `t` in `obligations`, returning `cache.local.exprType[e]`
  /// if it isn't `nil` or `t` otherwise.
  ///
  /// - Note: Unlike `assign(_:to:)`, this method doesn't override `inferredTypes[subject]` if
  ///   it isn't `nil` but creates an equality constraint instead.
  @discardableResult
  private mutating func constrain<T: ExprID>(
    _ e: T, to t: AnyType, in obligations: inout ProofObligations
  ) -> AnyType {
    if t[.hasError] { obligations.setUnsatisfiable() }
    assert(cache.local.exprType[e] == nil, "type already inferred")

    // Accumulate constraints on previous choices.
    if let u = obligations.exprType[e] {
      if areEquivalent(t, u, in: program[e].scope) { return u }
      obligations.insert(EqualityConstraint(t, u, origin: .init(.structural, at: program[e].site)))
      return u
    }

    obligations.assign(t, to: AnyExprID(e))
    return t
  }

  /// Proves the formulae in `obligations`, which relate to the well-typedness of `n`, returning
  /// the best assignment of universally quantified variables.
  @discardableResult
  private mutating func discharge<T: NodeIDProtocol>(
    _ obligations: ProofObligations, relatedTo n: T,
    ignoringSharedCache ignoreSharedCache: Bool = false
  ) -> Solution {
    let solution = tracingInference(relatedTo: n) { (me, loggingIsEnabled) in
      if obligations.isUnsatisfiable {
        // Nothing to do if the obligations are known unsatisfiable.
        return .init()
      } else {
        var system = ConstraintSystem(obligations, logging: loggingIsEnabled)
        return system.solution(querying: &me)
      }
    }

    commit(solution, satisfying: obligations, ignoringSharedCache: ignoreSharedCache)
    return solution
  }

  /// Commits the choices made in `solution` to satisfy `obligations` in the program.
  private mutating func commit(
    _ solution: Solution, satisfying obligations: ProofObligations,
    ignoringSharedCache ignoreSharedCache: Bool
  ) {
    for (n, r) in solution.bindings {
      var s = solution.substitutions.reify(reference: r, withVariables: .kept)

      let t = solution.substitutions.reify(obligations.exprType[n]!, withVariables: .kept)
      if t[.hasVariable] || s.arguments.values.contains(where: { $0.isTypeVariable }) {
        report(.error(notEnoughContextToInferArgumentsAt: program[n].site))
        s = solution.substitutions.reify(reference: s, withVariables: .substitutedByError)
      }

      cache.write(s, at: \.referredDecl[n], ignoringSharedCache: ignoreSharedCache)
    }

    for (c, o) in solution.callOperands {
      cache.write(o, at: \.callOperands[c], ignoringSharedCache: ignoreSharedCache)
    }

    for (e, t) in obligations.exprType {
      let u = solution.substitutions.reify(t, withVariables: .substitutedByError)
      cache.write(u, at: \.exprType[e], ignoringSharedCache: ignoreSharedCache)
    }

    // TODO: Patterns

    // Note: Post-inference checks run after other choices have been committed.
    for (d, t) in obligations.declType {
      let u = solution.substitutions.reify(t, withVariables: .substitutedByError)
      cache.uncheckedType[d].updateMonotonically(.computed(u))
      checkPostInference(d, solution: solution, ignoringSharedCache: ignoreSharedCache)
    }

    report(solution.diagnostics.elements)
    assert(solution.isSound || diagnostics.containsError, "inference failed without diagnostics")
  }

  /// Calls `action` on `self`, logging a trace of constraint solving iff `shouldTraceInference(n)`
  /// returns `true`.
  private mutating func tracingInference<T: NodeIDProtocol>(
    relatedTo n: T, _ action: (inout Self, Bool) -> Solution
  ) -> Solution {
    guard let f = shouldTraceInference, f(AnyNodeID(n), program) else {
      return action(&self, false)
    }

    print("\(program[n].site): type inference for '\(program[n])'")
    print("---")
    let s = action(&self, true)
    print(s)
    print("---")
    return s
  }

  /// Returns the rank of `lhs` relative ro `rhs`.
  mutating func rank(_ lhs: Solution, _ rhs: Solution) -> StrictPartialOrdering {
    var ranking: StrictPartialOrdering = .equal
    var namesInCommon = 0

    for (n, lhs) in lhs.bindings {
      guard let rhs = rhs.bindings[n] else { continue }
      namesInCommon += 1

      // Nothing to do if both functions have the same binding.
      if lhs == rhs { continue }

      let o = compareBindingPrecedence(
        lhs.decl!, rhs.decl!, in: program[n].scope, at: program[n].site)
      switch o {
      case .ascending:
        if ranking == .descending { return nil }
        ranking = .ascending
      case .descending:
        if ranking == .ascending { return nil }
        ranking = .descending
      default:
        return nil
      }
    }

    if lhs.bindings.count < rhs.bindings.count {
      if namesInCommon == lhs.bindings.count {
        return ranking != .ascending ? .descending : nil
      } else {
        return nil
      }
    }

    if lhs.bindings.count > rhs.bindings.count {
      if namesInCommon == rhs.bindings.count {
        return ranking != .descending ? .ascending : nil
      } else {
        return nil
      }
    }

    return namesInCommon == lhs.bindings.count ? ranking : nil
  }

  /// Compares `lhs` and `rhs` in `scopeOfUse` and returns whether one has either shadows or is
  /// more specific than the other.
  ///
  /// `lhs` and `rhs` are assumed to have compatible types.
  private mutating func compareBindingPrecedence(
    _ lhs: AnyDeclID, _ rhs: AnyDeclID, in scopeOfUse: AnyScopeID, at site: SourceRange
  ) -> StrictPartialOrdering {
    if let o = compareDepth(lhs, rhs, in: scopeOfUse) {
      return o
    }

    let t = uncheckedType(of: lhs)
    let u = uncheckedType(of: rhs)
    return compareSpecificity(t, u, in: scopeOfUse, at: site)
  }

  /// Compares `lhs` and `rhs` in `scopeOfUse` and returns whether one shadows the other.
  ///
  /// `lhs` is deeper than `rhs` w.r.t. `scopeOfUse` if any of these statements hold:
  /// - `lhs` and `rhs` are members of traits `t1` and `t2`, respectively, and `t1` refines `t2`.
  /// - `lhs` isn't member of a trait and `rhs` is.
  /// - `lhs` is lexically deeper than `rhs` (see `Program.compareLexicalDepth`).
  private mutating func compareDepth(
    _ lhs: AnyDeclID, _ rhs: AnyDeclID, in scopeOfUse: AnyScopeID
  ) -> StrictPartialOrdering {
    if let l = traitDeclaring(lhs) {
      // If `lhs` is a trait member but `rhs` isn't, then `rhs` shadows `lhs`.
      guard let r = traitDeclaring(rhs) else { return .descending }

      // If `lhs` and `rhs` are members of traits `t1` and `t2`, respectively, then `lhs` shadows
      // `rhs` iff `t1` refines `t2`.
      if isStrictRefinement(l, of: r) { return .ascending }
      if isStrictRefinement(r, of: l) { return .descending }
      return nil
    }

    if traitDeclaring(rhs) != nil {
      // If `rhs` is a trait member but `lhs` isn't, then `lhs` shadows `rhs`.
      return .ascending
    }

    return program.compareLexicalDepth(lhs, rhs, in: scopeOfUse)
  }

  /// Compares `lhs` and `rhs` in `scopeOfUse` and returns whether one is more specific than the
  /// other, instantiating generic type constraints at `site`.
  ///
  /// `lhs` is more specific than `rhs` iff both `lhs` and `rhs` are callable types with the same
  /// labels and `lhs` accepts strictly less arguments than `rhs`.
  private mutating func compareSpecificity(
    _ lhs: AnyType, _ rhs: AnyType, in scopeOfUse: AnyScopeID, at site: SourceRange
  ) -> StrictPartialOrdering {
    guard
      let l = lhs.base as? CallableType,
      let r = rhs.base as? CallableType
    else { return nil }

    guard
      l.inputs.count == r.inputs.count,
      l.inputs.elementsEqual(r.inputs, by: { $0.label == $1.label })
    else { return nil }

    let lRefinesR = isMoreSpecific(lhs, rhs, in: scopeOfUse, at: site)
    let rRefinesL = isMoreSpecific(rhs, lhs, in: scopeOfUse, at: site)

    if lRefinesR {
      return rRefinesL ? nil : .ascending
    }
    if rRefinesL {
      return lRefinesR ? nil : .descending
    }
    return nil
  }

  /// Returns `true` iff `lhs` is more specific than `rhs` in `scopeOfUse`, instantiating generic
  /// type constraints at `site`.
  ///
  /// - Requires: `lhs` and `rhs` are `CallableType`s.
  private mutating func isMoreSpecific(
    _ lhs: AnyType, _ rhs: AnyType, in scopeOfUse: AnyScopeID, at site: SourceRange
  ) -> Bool {
    // Open the right operand.
    let openedRight = open(type: rhs, at: site)
    var constraints = openedRight.constraints

    // Create pairwise subtyping constraints on the parameters.
    let l = lhs.base as! CallableType
    let r = openedRight.shape.base as! CallableType
    for (a, b) in zip(l.inputs, r.inputs) {
      constraints.insert(SubtypingConstraint(a.type, b.type, origin: .init(.binding, at: site)))
    }

    // Solve the constraint system.
    var obligations = ProofObligations(scope: scopeOfUse)
    obligations.insert(constraints)

    var s = ConstraintSystem(obligations, logging: false)
    return !s.solution(querying: &self).isSound
  }

  // MARK: AST Restructuring

  /// Returns a binary tree encoding the evaluation order of `e` or `nil` if `e` contains an
  /// undefined operator.
  private mutating func fold(_ e: SequenceExpr.ID) -> FoldedSequenceExpr? {
    if let tree = cache.local.foldedForm[e] { return tree }

    guard let tree = fold(program[e].tail[0...], into: .leaf(program[e].head)) else { return nil }
    cache.write(tree, at: \.foldedForm[e], ignoringSharedCache: true)
    return tree
  }

  /// Returns a copy of `initialResult` in which `tail` has been incorporated or `nil` if `tail`
  /// contains an undefined operator.
  private mutating func fold(
    _ tail: ArraySlice<SequenceExpr.TailElement>,
    into initialResult: FoldedSequenceExpr
  ) -> FoldedSequenceExpr? {
    var accumulator = initialResult

    for i in tail.indices {
      // Search for the operator declaration.
      let stem = program[tail[i].operator].name.value.stem
      let candidates = lookup(operator: stem, used: .infix, in: program[tail[i].operator].scope)

      switch candidates.count {
      case 0:
        report(.error(undefinedOperator: stem, at: program[tail[i].operator].site))
        return nil

      case 1:
        let precedence = program[candidates[0]].precedenceGroup?.value
        accumulator.append(
          operator: .init(expr: tail[i].operator, precedence: precedence),
          right: tail[i].operand)

      default:
        // TODO: should probably emit a diagnostic. Operator declarations cannot be overloaded.
        UNIMPLEMENTED()
      }
    }

    return accumulator
  }

  // MARK: Helpers

  /// Creates a fresh type variable.
  ///
  /// The returned instance is unique access concurrent type checker instances.
  mutating func freshVariable() -> TypeVariable {
    defer { nextFreshVariableIdentifier += 1 }
    return .init(nextFreshVariableIdentifier)
  }

  /// Creates a fresh term variable.
  ///
  /// The returned instance is unique access concurrent type checker instances.
  mutating func freshTermVariable() -> TermVariable {
    defer { nextFreshVariableIdentifier += 1 }
    return .init(nextFreshVariableIdentifier)
  }

  /// Returns `true` iff `t` is known as an arrow type.
  private func isArrow(_ t: AnyType) -> Bool {
    (t.base as? CallableType)?.isArrow ?? false
  }

  /// Returns `true` iff `t` is known as a subscript type.
  private func isSubscript(_ t: AnyType) -> Bool {
    !isArrow(t)
  }

  /// Returns `true` iff `e` is bound to a nominal type declaration in `o`.
  private mutating func isBoundToNominalTypeDecl(_ e: AnyExprID, in o: ProofObligations) -> Bool {
    if let r = NameExpr.ID(e).flatMap({ o.referredDecl[$0] }) {
      return isBoundToNominalTypeDecl(r)
    } else {
      return false
    }
  }

  /// Returns `true` iff `r` is bound to a nominal type declaration.
  private mutating func isBoundToNominalTypeDecl(_ r: DeclReference) -> Bool {
    if let d = r.decl {
      return isNominalTypeDecl(d)
    } else {
      return (r == .builtinType) || (r == .compilerKnownType)
    }
  }

  /// Returns `true` iff `d` is a nominal type declaration.
  private mutating func isNominalTypeDecl(_ d: AnyDeclID) -> Bool {
    switch d.kind {
    case AssociatedTypeDecl.self, ProductTypeDecl.self, TypeAliasDecl.self:
      return true
    case GenericParameterDecl.self:
      return uncheckedType(of: d).base is MetatypeType
    default:
      return false
    }
  }

  /// Returns `true` iff `d` introduces `var` bindings.
  private func isVar(_ d: BindingDecl.ID) -> Bool {
    program[d].pattern.introducer.value == .var
  }

  /// Returns `true` iff `t` is the receiver of a trait declaration.
  private func isTraitReceiver(_ t: GenericTypeParameterType) -> Bool {
    program[t.decl].scope.kind == TraitDecl.self
  }

  /// Returns `true` iff `t` is a generic type parameter an associated type rooted at one.
  private func isAbstractAssociatedDomain(_ t: AnyType) -> Bool {
    switch t.base {
    case let u as AssociatedTypeType:
      return isAbstractAssociatedDomain(u.domain)
    case let u as ConformanceLensType:
      return isAbstractAssociatedDomain(u.subject)
    case let u:
      return u is GenericTypeParameterType
    }
  }

  /// Returns `true` if `d` isn't a trait requirement, an FFI, or an external function.
  private func requiresBody(_ d: FunctionDecl.ID) -> Bool {
    !(program.isRequirement(d) || program[d].isForeignInterface || program[d].isExternal)
  }

  /// Returns the trait whose `g` is the receiver, if any.
  private func traitIntroducing(_ g: GenericParameterDecl.ID) -> TraitType? {
    TraitDecl.ID(program[g].scope).map({ (d) in TraitType(d, ast: program.ast) })
  }

  /// Returns `true` iff control flow may jump to the statement after `s`.
  private mutating func canFallThrough<T: StmtID>(_ s: T) -> Bool {
    switch s.kind {
    case BreakStmt.kind, ContinueStmt.kind, ReturnStmt.kind:
      return false
    case BraceStmt.kind:
      return canFallThrough(BraceStmt.ID(s)!)
    case ExprStmt.kind:
      return canFallThrough(ExprStmt.ID(s)!)
    default:
      return true
    }
  }

  /// Returns `true` iff control flow may jump to the statement after `s`.
  private mutating func canFallThrough(_ s: BraceStmt.ID) -> Bool {
    if let last = program[s].stmts.last {
      return canFallThrough(last)
    } else {
      return true
    }
  }

  /// Returns `false` iff executing `s` always terminates the program.
  private mutating func canFallThrough(_ s: ExprStmt.ID) -> Bool {
    let e = program.ast[s].expr
    let t = checkedType(of: e)
    let u = canonical(t, in: program[e].scope)
    return !u.isNever
  }

  /// Returns how `a` and `b` are ordered.
  private mutating func compareOrder(
    _ a: TraitType, _ b: TraitType
  ) -> StrictOrdering {
    let ab = bases(of: a)
    let bb = bases(of: b)

    if ab.unordered.count > bb.unordered.count {
      return .descending  // !!! .ascending in Slava's work
    } else if ab.unordered.count == bb.unordered.count {
      return .init(between: a.decl.rawValue, and: b.decl.rawValue)
    } else {
      return .descending
    }
  }

  /// Returns how `a` and `b` are ordered.
  private mutating func compareOrder(
    _ a: RequirementSymbol, _ b: RequirementSymbol
  ) -> StrictOrdering {
    switch (a, b) {
    case (.associatedType(let l), .associatedType(let r)):
      if program[l].baseName == program[r].baseName {
        return compareOrder(program.traitDeclaring(l)!, program.traitDeclaring(r)!)
      } else {
        return .init(between: program[l].baseName, and: program[r].baseName)
      }

    case (.parameterType(let l), .parameterType(let r)):
      if let t = traitIntroducing(l), let u = traitIntroducing(r) {
        return compareOrder(t, u)
      } else {
        return .init(between: l.rawValue, and: r.rawValue)
      }

    case (.trait(let l), .trait(let r)):
      return compareOrder(TraitType(l, ast: program.ast), TraitType(r, ast: program.ast))

    default:
      return .init(between: a.kind, and: b.kind)
    }
  }

  /// Returns how `a` and `b` are ordered.
  private mutating func compareOrder(
    _ a: RequirementTerm, _ b: RequirementTerm
  ) -> StrictOrdering {
    if a.symbols.count == b.symbols.count {
      for i in a.symbols.indices {
        let c = compareOrder(a.symbols[i], b.symbols[i])
        if c != .equal { return c }
      }
      return .equal
    } else {
      return .init(between: a.symbols.count, and: b.symbols.count)
    }
  }

  /// Returns the requirement term corresponding to `t`.
  func buildTerm(_ t: AnyType) -> RequirementTerm {
    switch t.base {
    case let u as GenericTypeParameterType:
      return [.parameterType(u.decl)]
    case let u as AssociatedTypeType:
      return buildTerm(u.domain).appending(.associatedType(u.decl))
    default:
      return [.concrete(t)]
    }
  }

  // MARK: Caching

  /// A possibly shared instance of a typed program.
  struct Cache {

    /// A lookup table.
    typealias LookupTable = [String: Set<AnyDeclID>]

    /// A key in a type lookup table.
    typealias TypeLookupKey = ScopedValue<AnyType>

    /// Cached information about the extensions of a scope.
    struct ScopeExtensionCache {

      /// A table mapping an extension in a given scope to `true` iff that extension is bound.
      var unbound: BitArray

      /// A table mapping a type to its extensions in a given scope.
      var typeToExtension: [AnyType: [AnyDeclID]]

      /// Creates an instance representing cached information for `count` extensions.
      init(count: Int) {
        unbound = .init(repeating: true, count: count)
        typeToExtension = [:]
      }

    }

    /// The local instance being type checked.
    private(set) var local: TypedProgram

    /// The instance being collaboratively typed checked.
    private var shared: SharedMutable<TypedProgram>?

    /// The updates of the shared cache currently pending.
    private var pendingUpdates: [SynchronizationUpdate] = []

    /// The number of updates in `pendingUpdates` that should be synchronized early.
    private var earlyUpdateCount = 0

    /// The number of early updates that are accumulated before being synchronized.
    private static let earlyUpdateThreshold = 100

    /// The declarations being currently type checked.
    var declsUnderChecking = Set<AnyDeclID>()

    /// A map from declaration to its overarching type before it's been type checked.
    var uncheckedType = DeclProperty<Memo<AnyType>>()

    /// A map from declaration space to its members.
    ///
    /// This map serves as cache for `lookup(_:memberOf:exposedTo)`. At no point is it guaranteed
    /// to be complete.
    var scopeToMembers: [TypeLookupKey: LookupTable] = [:]

    /// A map from lexical scope to the names introduced in it.
    ///
    /// This map serves as cache for `names(introducedIn:)`.
    var scopeToNames: [AnyScopeID: LookupTable] = [:]

    /// A map from lexical scope to information about its extensions.
    ///
    /// This map serves as cache for `appendExtensions(declaredIn:extending:to:)`.
    var scopeToTypeToExtensions: [AnyScopeID: ScopeExtensionCache] = [:]

    /// A map from type to the traits to which in conforms in a given scope.
    ///
    /// This map serves as cache for `conformedTraits(of:in:)`.
    var typeToConformedTraits: [TypeLookupKey: Set<TraitType>] = [:]

    /// A map from type to its extensions in a given scope.
    ///
    /// This map serves as cache for `extensions(of:exposedTo:)`.
    var typeToExtensions: [TypeLookupKey: [AnyDeclID]] = [:]

    /// A map from trait to its bases (i.e., the traits that it refines).
    ///
    /// This map serves as cache for `bases(of:)`.
    var traitToBases: [TraitType: RefinementClosure] = [:]

    /// A map from trait to its direct successors in the trait dependency graph.
    ///
    /// This map serves as cache for `successors(of:)`.
    var traitToSuccessors: [TraitDecl.ID: [TraitType]] = [:]

    /// A map from generic declarations to their (partially formed) environment.
    var partiallyFormedEnvironment: [AnyDeclID: GenericEnvironment] = [:]

    /// The strongly connected components of the trait dependency graph.
    var traitDependencyComponents = StronglyConnectedComponents<TraitType>()

    /// Creates an instance for memoizing type checking results in `local` and comminicating them
    /// to concurrent type checkers using `shared`.
    init(local: TypedProgram, shared: SharedMutable<TypedProgram>? = nil) {
      self.local = local
      self.shared = shared
    }

    /// Returns the value of the cache at `path`.
    ///
    /// The value at `path` in `self.local` is read and returned if it isn't `nil`. Otherwise, the
    /// value at `path` in `self.shared` is read, stored in `self.local`, and returned if it isn't
    /// `nil`, unless `self.cache` is `nil` or `ignoreSharedCache` is true.
    mutating func read<V>(
      _ path: WritableKeyPath<TypedProgram, V?>,
      ignoringSharedCache ignoreSharedCache: Bool = false
    ) -> V? {
      if let v = local[keyPath: path] {
        return v
      }
      if ignoreSharedCache { return nil }

      guard let v = shared?.read(applying: { $0[keyPath: path] })
      else { return nil }

      local[keyPath: path] = v
      return v
    }

    /// Writes `value` to the cache at `path`, applying the update with `merge`.
    ///
    /// After the call, `self.local[keyPath: path] == value`. If `self.shared` isn't `nil`, the
    /// update is recorded for the next synchronization round and `self.earlyUpdateCount` is
    /// incremented, unless `ignoreSharedCache` is `true`.
    ///
    /// `merge` asserts that the update is monotonic.
    mutating func write<V>(
      _ value: V, at path: WritableKeyPath<TypedProgram, V>,
      ignoringSharedCache ignoreSharedCache: Bool = false,
      mergingWith merge: @escaping (inout V, V) -> Void
    ) {
      local.write(value, at: path, mergingWith: merge)

      if shared != nil {
        func update(
          _ value: Any, at path: PartialKeyPath<TypedProgram>, in program: inout TypedProgram
        ) {
          let p = path as! WritableKeyPath<TypedProgram, V>
          merge(&program[keyPath: p], value as! V)
        }

        pendingUpdates.append(.init(path, applying: update))
        if !ignoreSharedCache {
          earlyUpdateCount += 1
        }
        synchronizeIfThresholdReached()
      }
    }

    /// Writes `value` to the cache at `path`, applying the update with `merge`.
    ///
    /// After the call, `self.local[keyPath: path] == value`. If `self.shared` isn't `nil`, the
    /// update is recorded for the next synchronization round and `self.earlyUpdateCount` is
    /// incremented, unless `ignoreSharedCache` is `true`.
    mutating func write<V>(
      _ value: V, at path: WritableKeyPath<TypedProgram, V>,
      ignoringSharedCache ignoreSharedCache: Bool = false
    ) where V: Monotonic {
      write(value, at: path) { (u, v) in u.updateMonotonically(v) }
    }

    /// Applies `self.read(path)`.
    subscript<V>(m: WritableKeyPath<TypedProgram, V?>) -> V? where V: Equatable {
      mutating get { read(m) }
    }

    /// Applies all pending updates to the shared instance iff `earlyUpdateThreshold` has been
    /// reached, resetting `self.earlyUpdateCount`.
    private mutating func synchronizeIfThresholdReached() {
      if earlyUpdateCount >= Self.earlyUpdateThreshold { synchronize() }
    }

    /// Applies all pending updates to the shared instance.
    fileprivate mutating func synchronize() {
      shared?.modify { (p) in
        for u in pendingUpdates {
          u.apply(local[keyPath: u.pathToUpdate], u.pathToUpdate, &p)
        }
      }
      pendingUpdates.removeAll(keepingCapacity: true)
      earlyUpdateCount = 0
    }

  }

  /// A synchronization update to perform on a shared instance.
  private struct SynchronizationUpdate: Hashable {

    /// A closure that accepts a `path` in `instance` and a `value` to write.
    typealias Apply = (
      _ value: Any,
      _ path: PartialKeyPath<TypedProgram>,
      _ instance: inout TypedProgram
    ) -> Void

    /// The path to the value to update.
    let pathToUpdate: PartialKeyPath<TypedProgram>

    /// A closure executing the update.
    let apply: Apply

    /// Hashes the salient parts of `self` into `hasher`.
    func hash(into hasher: inout Hasher) {
      hasher.combine(pathToUpdate)
    }

    /// Returns `true` iff `l` is equal to `r`.
    static func == (l: Self, r: Self) -> Bool {
      l.pathToUpdate == r.pathToUpdate
    }

    /// Creates an instance that writes `value` at `pathToUpdate` in a typed program.
    init(_ pathToUpdate: PartialKeyPath<TypedProgram>, applying apply: @escaping Apply) {
      self.pathToUpdate = pathToUpdate
      self.apply = apply
    }

  }

}

/// An AST visitation callback that collects recursive references to specific declarations.
private struct RecursiveReferenceRecognizer: ASTWalkObserver {

  /// The declarations to consider while looking for cycles.
  let targets: [AnyDeclID]

  /// A map from name expression to its referred declaration.
  let referredDecl: BindingMap

  /// The recursive references that have been found.
  var recursiveReferences: [NameExpr.ID] = []

  mutating func willEnter(_ n: AnyNodeID, in ast: AST) -> Bool {
    if let e = NameExpr.ID(n), let d = referredDecl[e]?.decl, targets.contains(d) {
      recursiveReferences.append(e)
    }
    return true
  }

}

extension Program {

  /// Returns a reference to `d` as a member of `parent`, specialized by `specialization`, exposed
  /// to `scopeOfUse`, and used as a constructor if `isConstructor` is `true`.
  fileprivate func makeReference(
    to d: AnyDeclID, specializedBy specialization: GenericArguments,
    memberOf parent: NameResolutionContext?,
    exposedTo scopeOfUse: AnyScopeID,
    usedAsConstructor isConstructor: Bool
  ) -> DeclReference {
    if isConstructor {
      return .constructor(InitializerDecl.ID(d)!, specialization)
    } else if isNonStaticMember(d) && !(parent?.type.base is MetatypeType) {
      if let p = parent {
        return .member(d, specialization, p.receiver!)
      } else {
        let r = innermostReceiver(in: scopeOfUse)!
        return .member(d, specialization, .elided(.direct(AnyDeclID(r), .empty)))
      }
    } else {
      return .direct(d, specialization)
    }
  }

}
