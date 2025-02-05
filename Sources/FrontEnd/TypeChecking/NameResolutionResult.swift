/// The result of a name resolution request.
enum NameResolutionResult: Sendable {

  /// Name resolution applied on the nominal prefix that doesn't require any overload resolution.
  /// The payload contains the collections of resolved and unresolved components.
  ///
  /// - Invariant: `resolved` is not empty.
  case done(resolved: [ResolvedComponent], unresolved: [NameExpr.ID])

  /// Name resolution failed.
  case failed

  /// Name resolution couldn't complete because the first component of the expression couldn't be
  /// resolved without type inference. The payload contains the type of the resolved part, unless
  /// it was left implicit, and the remaining unresolved components.
  ///
  /// - Invariant: `components` is not empty.
  case canceled(AnyType?, _ components: [NameExpr.ID])

  /// The result of name resolution for a single name component.
  struct ResolvedComponent: Sendable {

    /// The resolved component.
    let component: NameExpr.ID

    /// The declarations to which the component may refer.
    let candidates: [Candidate]

    /// Creates an instance with the given properties.
    init(_ component: NameExpr.ID, _ candidates: [Candidate]) {
      self.component = component
      self.candidates = candidates
    }

  }

  /// A candidate found by name resolution.
  struct Candidate: Sendable {

    /// Declaration being referenced.
    let reference: DeclReference

    /// The type of the declaration.
    let type: AnyType

    /// The constraints related to the open variables in `type`, if any.
    let constraints: ConstraintSet

    /// The diagnostics associated with to this candidate, if any.
    let diagnostics: DiagnosticSet

    /// Creates an instance with the given properties.
    init(
      reference: DeclReference, type: AnyType, constraints: ConstraintSet,
      diagnostics: DiagnosticSet
    ) {
      self.reference = reference
      self.type = type
      self.constraints = constraints
      self.diagnostics = diagnostics
    }

    /// Creates an instance denoting a built-in function, calling `freshVariable` to create fresh
    /// type variables.
    init(_ f: BuiltinFunction, makingFreshVariableWith freshVariable: () -> TypeVariable) {
      self.reference = .builtinFunction(f)
      self.type = ^f.type(makingFreshVariableWith: freshVariable)
      self.constraints = []
      self.diagnostics = []
    }

    /// Creates an instance denoting a built-in type.
    init(_ t: BuiltinType) {
      precondition(t != .module)
      self.reference = .builtinType
      self.type = ^MetatypeType(of: t)
      self.constraints = []
      self.diagnostics = []
    }

    /// A candidate denoting a reference to the built-in module.
    static var builtinModule = Candidate(
      reference: .builtinModule,
      type: .builtin(.module),
      constraints: [],
      diagnostics: [])

    /// Creates an instance denoting an compiler-known type.
    static func compilerKnown(_ t: AnyType) -> Self {
      .init(reference: .compilerKnownType, type: t, constraints: [], diagnostics: [])
    }

  }

  /// A set of candidates found by name resolution.
  struct CandidateSet: ExpressibleByArrayLiteral, Sendable {

    /// The candidates in the set.
    internal private(set) var elements: [Candidate] = []

    /// The positions of candidates in `elements` that are considered viable.
    internal private(set) var viable: [Int] = []

    /// Creates an instance from an array literal.
    init(arrayLiteral candidates: Candidate...) {
      for c in candidates { insert(c) }
    }

    /// Inserts `c` into `self`.
    mutating func insert(_ c: Candidate) {
      if !c.diagnostics.containsError {
        viable.append(elements.count)
      }
      elements.append(c)
    }

    /// Inserts the contents of `other` into `self`.
    mutating func formUnion(_ other: Self) {
      for c in other.elements { insert(c) }
    }

    /// Filters the viable candidates in `self` to keep those callable with given `labels`, unless
    /// no viable candidate satisfies this predicate.
    mutating func filter(accepting labels: [String?]) {
      if viable.count <= 1 { return }

      var filtered: [Int] = []
      for c in viable {
        guard let t = elements[c].type.base as? CallableType else { continue }
        if t.accepts(labels) {
          filtered.append(c)
        }
      }

      if !filtered.isEmpty {
        viable = filtered
      }
    }

  }

}
