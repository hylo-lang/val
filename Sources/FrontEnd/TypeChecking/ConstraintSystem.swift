import Utils

/// A collection of constraints over a set of open type variables and a set of unresolved name
/// expressions.
struct ConstraintSystem {

  /// The scope in which the goals are solved.
  private let scope: AnyScopeID

  /// The type checker used to query type relations and resolve names.
  private var checker: TypeChecker! = nil

  /// The goals in the system.
  private var goals: [Constraint] = []

  /// A map from goal its outcome.
  ///
  /// - Invariant: This array has the same length as `this.goals`.
  private var outcomes: OutcomeMap = []

  /// The fresh goals to solve.
  private var fresh: [GoalIdentity] = []

  /// The goals that are currently stale.
  private var stale: [GoalIdentity] = []

  /// The root goals that could not be solved.
  private var failureRoots: [GoalIdentity] = []

  /// A map from open type or term variable to its assignment.
  ///
  /// This map is monotonically extended during constraint solving to assign a type or term to each
  /// open variable in the constraint system. A system is complete if it can be used to derive a
  /// complete substitution map w.r.t. its open variables.
  private var substitutions = SubstitutionMap()

  /// A map from name expression to its referred declaration.
  ///
  /// This map is monotonically extended during constraint solving to assign a declaration to each
  /// unresolved name expression in the constraint system. A system is complete if it can be used
  /// to derive a complete name binding map w.r.t. its unresolved name expressions.
  private var bindings: [NameExpr.ID: DeclReference]

  /// A map from call expression to its operands after desugaring and implicit resolution.
  private var callOperands: [CallID: [ArgumentResolutionResult]] = [:]

  /// The penalties associated with the constraint system.
  ///
  /// This value serves to prune explorations that cannot produce a better solution than one
  /// already computed.
  private var penalties: Int = 0

  /// Indicates whether this instance should log a trace.
  private let loggingIsEnabled: Bool

  /// The current indentation level for logging messages.
  private var indentation = 0

  /// Creates an instance for solving the constraints in `obligations`, logging a trace of the
  /// deduction process if `loggingIsEnabled` is `true`.
  init(_ obligations: ProofObligations, logging loggingIsEnabled: Bool) {
    self.scope = obligations.scope
    self.bindings = obligations.referredDecl
    self.loggingIsEnabled = loggingIsEnabled
    _ = insert(fresh: obligations.constraints)
  }

  /// Creates an instance copying the state of `other`.
  private init(copying other: Self) {
    self.scope = other.scope
    self.goals = other.goals
    self.outcomes = other.outcomes
    self.fresh = other.fresh
    self.stale = other.stale
    self.failureRoots = other.failureRoots
    self.substitutions = other.substitutions
    self.bindings = other.bindings
    self.callOperands = other.callOperands
    self.penalties = other.penalties
    self.loggingIsEnabled = other.loggingIsEnabled
    self.indentation = other.indentation
  }

  /// Solves this instance, using `checker` to query type relations and resolve names and returning
  /// the best solution found.
  mutating func solution(querying checker: inout TypeChecker) -> Solution {
    solution(notWorseThan: .worst, querying: &checker)!
  }

  /// Solves this instance and returns the best solution with a score inferior or equal to
  /// `self.maxScore`, or `nil` if no such solution can be found.
  private mutating func solution(
    notWorseThan maxScore: Solution.Score,
    querying checker: inout TypeChecker
  ) -> Solution? {
    self.checker = consume checker
    defer { checker = self.checker.release() }

    logState()
    log("steps:")

    while let g = fresh.popLast() {
      // Make sure the current solution is still worth exploring.
      if score() > maxScore {
        log("- abort")
        return nil
      }

      goals[g].modifyTypes { (t) in
        substitutions.reify(t, withVariables: .kept)
      }

      log("- solve: \"\(goals[g])\"")
      indentation += 1
      log("actions:")
      defer { indentation -= 1 }

      if let s = solve(g) { return s }
    }

    return formSolution()
  }

  /// Eliminates `g`, storing the necessary assumptions about its open variables in `self` and
  /// returning a solution if there are no more goals to solve.
  private mutating func solve(_ g: GoalIdentity) -> Solution? {
    switch goals[g] {
    case is ConformanceConstraint:
      setOutcome(solve(conformance: g), for: g)
    case is EqualityConstraint:
      setOutcome(solve(equality: g), for: g)
    case is SubtypingConstraint:
      setOutcome(solve(subtyping: g), for: g)
    case is ParameterConstraint:
      setOutcome(solve(parameter: g), for: g)
    case is MemberConstraint:
      setOutcome(solve(member: g), for: g)
    case is TupleMemberConstraint:
      setOutcome(solve(tupleMember: g), for: g)
    case is CallConstraint:
      setOutcome(solve(call: g), for: g)
    case is MergingConstraint:
      setOutcome(solve(merging: g), for: g)
    case is DisjunctionConstraint:
      return solve(disjunction: g)
    case is OverloadConstraint:
      return solve(overload: g)
    default:
      unreachable()
    }

    return nil
  }

  /// Returns the currently known cost of the solution being computed.
  ///
  /// The cost of a solution increases monotonically when a constraint is eliminated.
  private func score() -> Solution.Score {
    .init(errorCount: failureRoots.count, penalties: penalties)
  }

  /// Returns `true` iff the solving `g` failed and `g` isn't subordinate.
  private func isFailureRoot(_ g: GoalIdentity) -> Bool {
    (goals[g].origin.parent == nil) && (outcomes.succeeded(g) == false)
  }

  /// Records the outcome `o` for the goal `key`.
  private mutating func setOutcome(_ o: Outcome?, for key: GoalIdentity) {
    log(outcome: o)
    assert(outcomes[key] == nil)
    outcomes[key] = o

    if isFailureRoot(key) {
      failureRoots.append(key)
    }
  }

  /// Creates a solution from the current state.
  ///
  /// - Requires: There is no fresh goal to solve left.
  private mutating func formSolution() -> Solution {
    assert(outcomes.enumerated().allSatisfy({ (i, o) in (o != nil) || stale.contains(i) }))
    for g in stale {
      setOutcome(.failure({ (_, _, _) in () }), for: g)
    }

    let m = substitutions.optimized()
    var d = DiagnosticSet()
    for (k, v) in zip(goals.indices, outcomes) where isFailureRoot(k) {
      v!.diagnoseFailure!(&d, m, outcomes)
    }

    return Solution(
      substitutions: m, bindings: bindings, callOperands: callOperands,
      penalties: penalties, diagnostics: d, stale: stale.map({ goals[$0] }))
  }

  /// Creates an ambiguous solution, reporting the ambiguity with `d`.
  ///
  /// The return value is the intersection of the choices and diagnostics that are identical in
  /// each result along with an additional diagnostic describing the ambiguity.
  ///
  /// - Requires: `result` contains at least two elements.
  private func formAmbiguousSolution<T>(
    _ results: Explorations<T>, diagnosedBy d: Diagnostic
  ) -> Solution {
    let (first, others) = results.elements.headAndTail!
    var s = others.reduce(into: first.solution, { (s, r) in s.formIntersection(r.solution) })
    s.incorporate(d)
    return s
  }

  /// Determines whether `g.model` conforms to `g.concept` and returns: `.success` if it conforms
  /// explicitly, `.product` if it may conform structurally,`.failure` if it doesn't conform, or
  /// `nil` if neither of these outcomes can be be determined yet.
  private mutating func solve(conformance g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! ConformanceConstraint

    // Nothing to do if the subject is still a type variable.
    if goal.model.base is TypeVariable {
      postpone(g)
      return nil
    }

    // Check whether the conformance holds, either explicitly or structually.
    if checker.conforms(goal.model, to: goal.concept, in: scope) {
      return .success
    } else {
      return .failure(failureToSolve(goal))
    }
  }

  /// Returns a closure diagnosing a failure to solve `goal`.
  private mutating func failureToSolve(_ goal: ConformanceConstraint) -> DiagnoseFailure {
    return { (d, m, _) in
      let t = m.reify(goal.model)
      d.insert(.error(t, doesNotConformTo: goal.concept, at: goal.origin.site))
    }
  }

  /// Returns eiteher `.success` if `g.left` is unifiable with `g.right` or `.failure` otherwise.
  private mutating func solve(equality g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! EqualityConstraint
    return solve(goal.left, equals: goal.right, for: g, failure: { $0.failureToSolve(goal) })
  }

  private mutating func solve(
    _ l: AnyType, equals r: AnyType, for g: GoalIdentity,
    failure: (inout Self) -> DiagnoseFailure
  ) -> Outcome? {
    switch solve(l, equals: r) {
    case .some(true):
      return .success
    case .some(false):
      return .failure(failure(&self))
    case .none:
      postpone(g)
      return nil
    }
  }

  /// Returns a closure diagnosing a failure to solve `goal`.
  private mutating func failureToSolve(_ goal: EqualityConstraint) -> DiagnoseFailure {
    { (d, m, _) in
      let (l, r) = (m.reify(goal.left), m.reify(goal.right))
      switch goal.origin.kind {
      case .whereClause:
        d.insert(.error(unsatisfiedWhereClauseAt: goal.origin.site))
      default:
        d.insert(.error(type: l, incompatibleWith: r, at: goal.origin.site))
      }
    }
  }

  /// Returns `.success` if `g.left` is subtype of `g.right`, `.failure` if it isn't, `.product`
  /// if `g` must be broken down to smaller goals, or `nil` if that can't be determined yet.
  ///
  /// If the constraint is strict, then `g.left` must be different than `g.right`.
  private mutating func solve(subtyping g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! SubtypingConstraint
    lazy var o = goal.origin.subordinate()

    // Note: we're not using canonical equality here since we'll be dealing with aliases and
    // structural equivalences during unification anyway.
    if goal.left == goal.right {
      return goal.isStrict ? .failure(failureToSolve(goal)) : .success
    }

    switch (goal.left.base, goal.right.base) {
    case (let l as TypeAliasType, let r as TypeAliasType):
      return simplify(goal, as: l.resolved, isSubtypeOf: r.resolved)

    case (let l as TypeAliasType, _):
      return simplify(goal, as: l.resolved, isSubtypeOf: goal.right)

    case (_, let r as TypeAliasType):
      return simplify(goal, as: goal.left, isSubtypeOf: r.resolved)

    case (let l as ArrowType, let r as ArrowType):
      return solve(subtyping: g, between: l, and: r)

    case (let l as UnionType, let r as UnionType):
      return solve(subtyping: g, between: l, and: r)

    case (_, let r as UnionType):
      // If `R` is an empty union, so must be `L`.
      if r.elements.isEmpty {
        return matches(goal.left, goal.right) ? .success : .failure(failureToSolve(goal))
      }

      // If `R` has a single element, it must be above (the canonical form of) `L`.
      if let e = r.elements.uniqueElement {
        let s = schedule(SubtypingConstraint(goal.left, e, origin: o))
        return delegate(to: [s])
      }

      // If `R` has multiple elements, then:
      // - if `L` can't be a union, `L` must be subtype of one element element in `R`;
      // - if the goal strict, `L` must be subtype of some strict subset of `R`;
      // - otherwise, `L` must be equal to `R` or a subtype of a subset of `R`.
      var candidates: [DisjunctionConstraint.Predicate] = []
      if !(goal.left.base is TypeVariable) {
        for e in r.elements {
          let c = SubtypingConstraint(goal.left, e, origin: o)
          candidates.append(.init(constraints: [c], penalties: 1))
        }
      } else {
        for subset in r.elements.combinations(ofCount: r.elements.count - 1) {
          let c = SubtypingConstraint(goal.left, ^UnionType(subset), origin: o)
          candidates.append(.init(constraints: [c], penalties: 1))
        }
        if !goal.isStrict {
          let c = EqualityConstraint(goal.left, goal.right, origin: o)
          candidates.append(.init(constraints: [c], penalties: 0))
        }
      }

      let s = schedule(DisjunctionConstraint(between: candidates, origin: o))
      return delegate(to: [s])

    case (_, _ as TypeVariable):
      // The type variable is above a more concrete type. We should compute the "join" of all types
      // to which `L` is coercible and that are below `R`, but that set is unbounded. We have no
      // choice but to postpone the goal.
      if goal.isStrict {
        postpone(g)
        return nil
      } else {
        let s = schedule(inferenceConstraint(goal.left, isSubtypeOf: goal.right, origin: o))
        return delegate(to: [s])
      }

    case (_ as TypeVariable, _):
      // The type variable is below a more concrete type. We should compute the "meet" of all types
      // coercible to `R` and that are above `L`, but that set is unbounded unless `R` is a leaf.
      // If it isn't, we have no choice but to postpone the goal.
      if goal.right.isLeaf {
        return solve(goal.left, equals: goal.right, for: g, failure: { $0.failureToSolve(goal) })
      } else if goal.isStrict {
        postpone(g)
        return nil
      } else {
        let s = schedule(inferenceConstraint(goal.left, isSubtypeOf: goal.right, origin: o))
        return delegate(to: [s])
      }

    case (let l as RemoteType, _):
      let s = schedule(
        SubtypingConstraint(l.bareType, goal.right, strictly: goal.isStrict, origin: o))
      return delegate(to: [s])

    case (_, let r as ExistentialType):
      guard r.constraints.isEmpty else { UNIMPLEMENTED() }

      // Penalize type coercion.
      penalties += 1

      switch r.interface {
      case .traits(let traits):
        if traits.isEmpty {
          // All types conform to `Any`.
          return .success
        } else {
          var subordinates: [GoalIdentity] = []
          for t in traits {
            subordinates.append(
              schedule(ConformanceConstraint(goal.left, conformsTo: t, origin: o)))
          }
          return delegate(to: subordinates)
        }

      case .generic(let r):
        let d: AnyDeclID
        switch r.base {
        case let u as ProductType:
          d = AnyDeclID(u.decl)
        case let u as TypeAliasType:
          d = AnyDeclID(u.decl)
        default:
          unreachable()
        }

        let r = checker.openForUnification(d)
        let s = schedule(EqualityConstraint(goal.left, ^r, origin: o))
        return delegate(to: [s])

      case .metatype:
        let r = MetatypeType(of: checker.freshVariable())
        let s = schedule(EqualityConstraint(goal.left, ^r, origin: o))
        return delegate(to: [s])
      }

    case (let l as AssociatedTypeType, _) where l.root.base is TypeVariable:
      postpone(g)
      return nil

    case (_, let r as AssociatedTypeType) where r.root.base is TypeVariable:
      postpone(g)
      return nil

    default:
      if !goal.left.isCanonical || !goal.right.isCanonical {
        let l = checker.canonical(goal.left, in: scope)
        let r = checker.canonical(goal.right, in: scope)
        let s = schedule(SubtypingConstraint(l, r, strictly: goal.isStrict, origin: o))
        return delegate(to: [s])
      } else if goal.isStrict {
        return .failure(failureToSolve(goal))
      } else {
        return solve(goal.left, equals: goal.right, for: g, failure: { $0.failureToSolve(goal) })
      }
    }
  }

  /// Implements of `solve(subtyping:)` for two `ArrowType`s.
  private mutating func solve(
    subtyping g: GoalIdentity, between l: ArrowType, and r: ArrowType
  ) -> Outcome? {
    let goal = goals[g] as! SubtypingConstraint

    if !l.labels.elementsEqual(r.labels) {
      return .failure(failureToSolve(goal))
    }

    if l.receiverEffect > r.receiverEffect {
      return .failure(failureToSolve(goal))
    }

    var subordinates: [GoalIdentity] = []
    let o = goal.origin.subordinate()
    subordinates.append(schedule(SubtypingConstraint(l.environment, r.environment, origin: o)))

    // Parameters are contravariant; return types are covariant.
    for (a, b) in zip(l.inputs, r.inputs) {
      subordinates.append(schedule(SubtypingConstraint(b.type, a.type, origin: o)))
    }
    subordinates.append(schedule(SubtypingConstraint(l.output, r.output, origin: o)))
    return .product(subordinates, failureToSolve(goal))
  }

  /// Implements of `solve(subtyping:)` for two `UnionType`s.
  private mutating func solve(
    subtyping g: GoalIdentity, between l: UnionType, and r: UnionType
  ) -> Outcome? {
    let goal = goals[g] as! SubtypingConstraint

    // If both types are unions, all elements in `L` must be contained in `R`.
    var subordinates: [GoalIdentity] = []
    let o = goal.origin.subordinate()
    for e in l.elements {
      subordinates.append(schedule(SubtypingConstraint(e, goal.right, origin: o)))
    }
    return .product(subordinates, failureToSolve(goal))
  }

  /// Returns the outcome of solving `subtype <: suprtype` as a simplification of `goal`.
  private mutating func simplify(
    _ goal: SubtypingConstraint, as subtype: AnyType, isSubtypeOf supertype: AnyType
  ) -> Outcome {
    let o = goal.origin.subordinate()
    let s = schedule(SubtypingConstraint(subtype, supertype, strictly: goal.isStrict, origin: o))
    return .product([s], failureToSolve(goal))
  }

  /// Returns a closure diagnosing a failure to solve `goal`.
  private mutating func failureToSolve(_ goal: SubtypingConstraint) -> DiagnoseFailure {
    { (d, m, _) in
      let (l, r) = (m.reify(goal.left), m.reify(goal.right))
      switch goal.origin.kind {
      case .initializationWithHint:
        d.insert(.error(cannotInitialize: r, with: l, at: goal.origin.site))
      case .initializationWithPattern:
        d.insert(.error(l, doesNotMatch: r, at: goal.origin.site))
      default:
        if goal.isStrict {
          d.insert(.error(l, isNotStrictSubtypeOf: r, at: goal.origin.site))
        } else {
          d.insert(.error(l, isNotSubtypeOf: r, at: goal.origin.site))
        }
      }
    }
  }

  /// Returns either `.success` if instances of `g.left` can be passed to a parameter `g.right`,
  /// `.failure` if they can't, or `nil` if neither of these outcomes can be determined yet.
  private mutating func solve(parameter g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! ParameterConstraint

    switch goal.right.base {
    case _ where checker.areEquivalent(goal.left, goal.right, in: scope):
      return .success

    case is TypeVariable:
      postpone(g)
      return nil

    case let p as ParameterType:
      if p.isAutoclosure {
        return solve(autoclosureParameter: goal, ofType: p)
      }
      let s = schedule(
        SubtypingConstraint(goal.left, p.bareType, origin: goal.origin.subordinate()))
      return .product([s]) { (d, m, r) in
        let (l, r) = (m.reify(goal.left), m.reify(goal.right))
        d.insert(.error(cannotPass: l, toParameter: r, at: goal.origin.site))
      }

    default:
      return .failure { (d, m, _) in
        d.insert(.error(invalidParameterType: m.reify(goal.right), at: goal.origin.site))
      }
    }
  }

  /// Returns either `.success` if instances of `goal.left` can be passed to a parameter `p`,
  /// `.failure` if they can't, or `nil` if neither of these outcomes can be determined yet.
  private mutating func solve(
    autoclosureParameter goal: ParameterConstraint, ofType p: ParameterType
  ) -> Outcome? {
    let t = ArrowType(p.bareType)!
    let s = schedule(
      ParameterConstraint(
        goal.left, AnyType(ParameterType(.`let`, t.output)), origin: goal.origin.subordinate()))
    // TODO: the env is not always .void
    let s1 = schedule(
      EqualityConstraint(.void, t.environment, origin: goal.origin.subordinate()))
    return .product([s, s1]) { (d, m, r) in
      let (l, r) = (m.reify(goal.left), m.reify(goal.right))
      d.insert(.error(cannotPass: l, toParameter: r, at: goal.origin.site))
    }
  }

  /// Returns either `.success` if `g.subject` has a member `g.memberName` of type `g.memberType`,
  /// `.failure` if it doesn't, `.product` if `g` must be broken down to smaller goals, or `nil` if
  /// if neither of these outcomes can be determined yet.
  private mutating func solve(member g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! MemberConstraint

    if goal.subject.base is TypeVariable {
      postpone(g)
      return nil
    }

    let n = SourceRepresentable(value: goal.memberName, range: goal.origin.site)

    let context = NameResolutionContext(
      type: goal.subject, receiver: .init(checker.program[goal.memberExpr].domain))
    let candidates = checker.resolve(
      n, specializedBy: [], in: context, exposedTo: scope, usedAs: goal.purpose)

    if candidates.elements.isEmpty {
      return .failure { (d, m, _) in
        let t = m.reify(goal.subject)
        d.insert(.error(undefinedName: goal.memberName, in: t, at: goal.origin.site))
      }
    }

    if candidates.viable.isEmpty {
      var reasons = DiagnosticSet()
      if let c = candidates.elements.uniqueElement {
        reasons.formUnion(c.diagnostics.elements)
      } else {
        reasons.insert(.error(noViableCandidateToResolve: n, notes: []))
      }
      return .failure({ (d, _, _) in d.formUnion(reasons) })
    }

    if let i = candidates.viable.uniqueElement {
      let c = candidates.elements[i]
      bindings[goal.memberExpr] = c.reference

      var subordinates = insert(fresh: c.constraints)
      subordinates.append(
        schedule(EqualityConstraint(c.type, goal.memberType, origin: goal.origin.subordinate())))
      return delegate(to: subordinates)
    }

    let selected = candidates.viable.map { (i) in
      let pick = candidates.elements[i]
      let penalties = pick.reference.decl.map({ checker.program.isRequirement($0) ? 1 : 0 }) ?? 0
      return OverloadConstraint.Predicate(pick, penalties: penalties)
    }

    let s = schedule(
      OverloadConstraint(
        goal.memberExpr, withType: goal.memberType, refersToOneOf: selected,
        origin: goal.origin.subordinate()))
    return delegate(to: [s])
  }

  /// Returns either `.success` if `g.subject` is a tuple type whose `g.elementIndex`-th element
  /// has type `g.elementType`, `.failure` if it doesn't, `.product` if `g` must be broken down to
  /// smaller goals, or `nil` if if neither of these outcomes can be determined yet.
  private mutating func solve(tupleMember g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! TupleMemberConstraint

    switch goal.subject.base {
    case is TypeVariable:
      postpone(g)
      return nil

    case let t as TupleType:
      if goal.elementIndex >= t.elements.count { break }
      let e = t.elements[goal.elementIndex].type
      let s = schedule(EqualityConstraint(e, goal.elementType, origin: goal.origin.subordinate()))
      return delegate(to: [s])

    case let t as TypeAliasType:
      let c = TupleMemberConstraint(
        t.aliasee.value, at: goal.elementIndex, hasType: goal.elementType,
        origin: goal.origin.subordinate())
      let s = schedule(c)
      return delegate(to: [s])

    default:
      // TODO: Handle bound generic types
      break
    }

    return .failure { (d, m, _) in
      let s = m.reify(goal.subject)
      d.insert(.error(undefinedName: goal.elementIndex, in: s, at: goal.origin.site))
    }
  }

  /// Returns either `.success` if `g.callee` is a callable type with parameters `g.parameters`
  /// and return type `g.output`, `.failure` if it doesn't, `.product` if `g` must be broken
  /// down to smaller goals, or `nil` if neither of these outcomes can be determined yet.
  private mutating func solve(call g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! CallConstraint

    if goal.callee.base is TypeVariable {
      postpone(g)
      return nil
    }

    guard let callee = goal.callee.base as? CallableType, goal.isArrow == callee.isArrow else {
      return .failure(invalidCallee(goal))
    }

    guard let argumentMatching = match(argumentsOf: goal, parametersOf: callee) else {
      return .failure { (d, m, _) in
        d.insert(
          .error(labels: goal.labels, incompatibleWith: callee.labels, at: goal.origin.site))
      }
    }

    callOperands[goal.call] = argumentMatching.pairings

    var subordinates: [GoalIdentity] = []
    for c in argumentMatching.constraints {
      subordinates.append(schedule(c))
    }

    // If the callee has a method type, its return type depends on whether it is used mutably.
    let o = callee.outputOfUse(mutable: goal.isMutating)
    subordinates.append(
      schedule(EqualityConstraint(o, goal.output, origin: goal.origin.subordinate())))

    return delegate(to: subordinates)
  }

  /// Returns a closure diagnosing a failure to solve `g` because of an invalid callee.
  private mutating func invalidCallee(_ g: CallConstraint) -> DiagnoseFailure {
    { (d, m, _) in
      if g.isArrow {
        d.insert(.error(cannotCall: m.reify(g.callee), as: .function, at: g.origin.site))
      } else {
        d.insert(.error(cannotCall: m.reify(g.callee), as: .subscript, at: g.origin.site))
      }
    }
  }

  /// Returns how the arguments in `goal` match the parameters of `callee`.
  private mutating func match(
    argumentsOf goal: CallConstraint, parametersOf callee: CallableType
  ) -> (constraints: [ParameterConstraint], pairings: [ArgumentResolutionResult])? {
    var constraints: [ParameterConstraint] = []
    var pairings: [ArgumentResolutionResult] = []

    var i = 0
    for j in callee.inputs.indices {
      let p = callee.inputs[j]

      // If there's an explicit argument, use it unless if has a different label.
      if (goal.arguments.count > i) && (goal.arguments[i].label?.value == p.label) {
        let a = goal.arguments[i]
        let o = ConstraintOrigin(.argument, at: goal.arguments[i].valueSite)
        constraints.append(ParameterConstraint(a.type, p.type, origin: o))
        pairings.append(.explicit(i))
        i += 1
        continue
      }

      // Check for an implicit definition if the parameter accepts implicit definitions.
      if callee.inputs[i].isImplicit {
        let t = ParameterType(callee.inputs[i].type)!
        if let d = checker.implicitArgument(to: t, exposedTo: scope) {
          pairings.append(.implicit(d))
          continue
        }
      }

      // Use the parameter's default value if available.
      if callee.inputs[i].hasDefault {
        pairings.append(.defaulted)
        continue
      }

      // Argument list does not match the parameter list.
      return nil
    }

    assert(pairings.count == callee.inputs.count)
    if i == goal.arguments.count {
      return (constraints, pairings)
    } else {
      return nil
    }
  }

  private mutating func solve(merging g: GoalIdentity) -> Outcome? {
    let goal = goals[g] as! MergingConstraint
    guard !goal.branches.isEmpty else { return .success }

    var subordinates: [GoalIdentity] = []
    let o = goal.origin.subordinate()
    for b in goal.branches {
      subordinates.append(schedule(SubtypingConstraint(goal.supertype, b, origin: o)))
    }
    return .product(subordinates) { (d, m, _) in
      let t = goal.branches.map({ m.reify($0) })
      d.insert(.error(conditionalHasMismatchingTypes: t, at: goal.origin.site))
    }
  }

  /// Solves the remaining goals separately for each choice in `g` and returns the best solution.
  private mutating func solve(disjunction g: GoalIdentity) -> Solution? {
    let goal = goals[g] as! DisjunctionConstraint

    let results: Explorations<DisjunctionConstraint> = explore(g) { (solver, choice) in
      solver.penalties += choice.penalties
      return solver.insert(fresh: choice.constraints)
    }

    if let pick = results.elements.uniqueElement?.solution {
      return pick
    } else if results.elements.isEmpty {
      return nil
    }

    return formAmbiguousSolution(
      results, diagnosedBy: .error(ambiguousDisjunctionAt: goal.origin.site))
  }

  /// Solves the remaining goals separately for each choice in `g` and returns the best solution.
  private mutating func solve(overload g: GoalIdentity) -> Solution? {
    let goal = goals[g] as! OverloadConstraint

    let results: Explorations<OverloadConstraint> = explore(g) { (solver, choice) in
      solver.penalties += choice.penalties
      solver.bindings[goal.overloadedExpr] = choice.reference
      return solver.insert(fresh: choice.constraints)
    }

    if let pick = results.elements.uniqueElement?.solution {
      return pick
    } else if results.elements.isEmpty {
      return nil
    }

    return formAmbiguousSolution(
      results,
      diagnosedBy: .error(
        ambiguousUse: goal.overloadedExpr,
        in: checker.program.ast,
        candidates: results.elements.compactMap(\.choice.reference.decl)))
  }

  /// Solves the remaining goals in `self` exploring each choice in `g` with a separate constraint
  /// systems configured with `configureSubSystem` returns the best solution of each exploration.
  ///
  /// - Parameters:
  ///   - g: the goal whose choices would be explored; must denote a constraint of type `T`.
  ///   - checker: an instance used to query type relations and resolve names.
  ///   - configureSubSystem: A closure that prepares a constraint system using one of `g`'s
  ///     choices and returns the identities of the goals added to that system.
  private mutating func explore<T: DisjunctiveConstraintProtocol>(
    _ g: GoalIdentity,
    configuringSubSystemWith configureSubSystem: (inout Self, T.Predicate) -> [GoalIdentity]
  ) -> Explorations<T> {
    log("- fork:")
    indentation += 1
    defer { indentation -= 1 }

    var results = Explorations<T>()
    for choice in (goals[g] as! T).choices {
      // Don't bother if there's no chance to find a better solution.
      var underestimatedChoiceScore = score()
      underestimatedChoiceScore.penalties += choice.penalties
      if underestimatedChoiceScore > results.score {
        log("- skip: \"\(choice)\"")
        continue
      }

      log("- pick: \"\(choice)\"")
      indentation += 1
      defer { indentation -= 1 }

      // Explore the result of this choice.
      var exploration = Self(copying: self)
      let s = configureSubSystem(&exploration, choice)
      exploration.setOutcome(s.isEmpty ? .success : delegate(to: s), for: g)
      guard let new = exploration.solution(notWorseThan: results.score, querying: &checker) else {
        continue
      }

      // Insert the new result.
      results.insert((choice, new), rankingSolutionWith: { (a, b) in checker.rank(a, b) })
    }

    return results
  }

  /// Returns an outcome indicating that a goal has been broken into given `subordinates` and
  /// forwards their diagnostics.
  private func delegate(to s: [GoalIdentity]) -> Outcome {
    .product(s) { (d, m, r) in
      for g in s where !(r.succeeded(g)!) {
        r[g]!.diagnoseFailure?(&d, m, r)
      }
    }
  }

  /// Schedules `g` to be solved in the future and returns its identity.
  private mutating func schedule(_ g: Constraint) -> GoalIdentity {
    log("- schedule: \"\(g)\"")
    return insert(fresh: g)
  }

  /// Inserts `g` into the fresh set and returns its identity.
  private mutating func insert(fresh g: Constraint) -> GoalIdentity {
    // Note: It could be worth looking for the index of a goal equal to `g` rather than appending
    // it unconditionally so that we don't solve the same constraint twice. However, efficient
    // lookup would require a set while we need constraint indices to be stable identities. One
    // solution would be to implement `goals` and `outcomes` as persistent data structures.
    let newIdentity = goals.count
    goals.append(g)
    outcomes.append(nil)

    // fresh is sorted in order of increasing simplicity.
    let newIdentityGoal = goals[newIdentity]
    let i = fresh.partitioningIndex(where: { goals[$0].isSimpler(than: newIdentityGoal) })
    fresh.insert(newIdentity, at: i)
    return newIdentity
  }

  /// Inserts `batch` into the fresh set.
  private mutating func insert<S: Sequence<Constraint>>(fresh batch: S) -> [GoalIdentity] {
    batch.map { (g) in insert(fresh: g) }
  }

  /// Schedules `g` to be solved only once the solver has inferred more information about at least
  /// one of its type variables.
  ///
  /// - Requires: `g` must involve type variables.
  private mutating func postpone(_ g: GoalIdentity) {
    stale.append(g)
  }

  /// Returns `true` iff `lhs` and `rhs` can be unified, updating the substitution table.
  ///
  /// Type unification consists of finding substitutions that makes `lhs` and `rhs` equal. Both
  /// types are visited in lockstep, updating `self.subscritutions` every time either side is a
  /// variable for which no substitution has been made yet.
  private mutating func solve(_ lhs: AnyType, equals rhs: AnyType) -> ThreeValuedBit {
    let t = checker.canonical(substitutions[lhs], in: scope)
    let u = checker.canonical(substitutions[rhs], in: scope)
    if !isUnifiable(t) || !isUnifiable(u) {
      return .none
    } else {
      return .some(matches(t, u))
    }
  }

  private func isUnifiable(_ t: AnyType) -> Bool {
    t.isCanonical && AssociatedTypeType(t).map(default: true, \.root.isVariable)
  }

  /// Returns `true` iff `lhs` and `rhs` can be unified.
  private mutating func unify(_ lhs: AnyType, _ rhs: AnyType) -> Bool {
    let t = substitutions[lhs]
    let u = substitutions[rhs]

    switch (t.base, u.base) {
    case (let l as TypeVariable, _):
      assume(l, equals: u)
      return true

    case (_, let r as TypeVariable):
      assume(r, equals: t)
      return true

    case (let l as UnionType, let r as UnionType):
      return unify(l, r)

    case _ where !t.isCanonical || !u.isCanonical:
      return matches(checker.canonical(t, in: scope), checker.canonical(u, in: scope))

    default:
      return checker.areEquivalent(t, u, in: scope)
    }
  }

  /// Returns `true` iff `lhs` and `rhs` can be unified.
  private mutating func unify(
    _ lhs: UnionType, _ rhs: UnionType
  ) -> Bool {
    for a in lhs.elements {
      var success = false
      for b in rhs.elements where matches(a, b) {
        success = true
      }
      if !success { return false }
    }
    return true
  }

  /// Returns `true` iff `lhs` and `rhs` can be unified.
  private mutating func unify(_ lhs: AnyTerm, _ rhs: AnyTerm) -> Bool {
    let t = substitutions[lhs]
    let u = substitutions[rhs]

    switch (t.base, u.base) {
    case (let l as TermVariable, _):
      assume(l, equals: u)
      return true

    case (_, let r as TermVariable):
      assume(r, equals: t)
      return true

    default:
      return t == u
    }
  }

  /// Returns `true` iff `t` and `u` are equal under some substitution of their variables.
  private mutating func matches(_ t: AnyType, _ u: AnyType) -> Bool {
    switch (t.base, u.base) {
    case (let lhs as BoundGenericType, let rhs as BoundGenericType):
      if lhs.arguments.count != rhs.arguments.count { return false }
      var result = matches(lhs.base, rhs.base)
      for (a, b) in zip(lhs.arguments, rhs.arguments) {
        result = matches(a.value, b.value) && result
      }
      return result

    case (let lhs as MetatypeType, let rhs as MetatypeType):
      return matches(lhs.instance, rhs.instance)

    case (let lhs as TupleType, let rhs as TupleType):
      if !lhs.labels.elementsEqual(rhs.labels) { return false }
      return matches(lhs.elements, rhs.elements, at: \.type)

    case (let lhs as ArrowType, let rhs as ArrowType):
      if !lhs.labels.elementsEqual(rhs.labels) { return false }
      var result = matches(lhs.inputs, rhs.inputs, at: \.type)
      result = matches(lhs.output, rhs.output) && result
      result = matches(lhs.environment, rhs.environment) && result
      return result

    case (let lhs as BufferType, let rhs as BufferType):
      return matches(lhs.element, rhs.element) && matches(lhs.count, rhs.count)

    case (let lhs as MethodType, let rhs as MethodType):
      if !lhs.labels.elementsEqual(rhs.labels) || (lhs.capabilities != rhs.capabilities) {
        return false
      }

      var result = matches(lhs.inputs, rhs.inputs, at: \.type)
      result = matches(lhs.output, rhs.output) && result
      result = matches(lhs.receiver, rhs.receiver) && result
      return result

    case (let lhs as ParameterType, let rhs as ParameterType):
      if lhs.access != rhs.access { return false }
      return matches(lhs.bareType, rhs.bareType)

    case (let lhs as RemoteType, let rhs as RemoteType):
      if lhs.access != rhs.access { return false }
      return matches(lhs.bareType, rhs.bareType)

    default:
      return (t == u) || unify(t, u)
    }
  }

  /// Returns `true` iff the result of `matches(_:_:)` applied on all elements from `ts` and `us`
  /// pairwise is `true`.
  private mutating func matches<T: Sequence>(
    _ ts: T, _ us: T, at p: KeyPath<T.Element, AnyType>
  ) -> Bool {
    var result = true
    for (a, b) in zip(ts, us) {
      result = matches(a[keyPath: p], b[keyPath: p]) && result
    }
    return result
  }

  /// Returns `true` iff `t` and `u` are equal under some substitution of their variables.
  private mutating func matches(_ t: AnyTerm, _ u: AnyTerm) -> Bool {
    (t == u) || unify(t, u)
  }

  /// Returns `true` iff `t` and `u` are equal under some substitution of their variables.
  private mutating func matches(_ t: CompileTimeValue, _ u: CompileTimeValue) -> Bool {
    switch (t, u) {
    case (.type(let lhs), .type(let rhs)):
      return matches(lhs, rhs)
    case (.term(let lhs), .term(let rhs)):
      return matches(lhs, rhs)
    default:
      return false
    }
  }

  /// Extends the type substution table to map `tau` to `substitute`.
  private mutating func assume(_ tau: TypeVariable, equals substitute: AnyType) {
    log("- assume: \"\(tau) = \(substitute)\"")
    substitutions.assign(substitute, to: tau)
    refresh()
  }

  /// Extends the term substution table to map `tau` to `substitute`.
  private mutating func assume(_ tau: TermVariable, equals substitute: AnyTerm) {
    log("- assume: \"\(tau) = \(substitute)\"")
    substitutions.assign(substitute, to: tau)
    refresh()
  }

  /// Refresh stale constraints containing variables that have been assigned.
  private mutating func refresh() {
    for i in (0 ..< stale.count).reversed() {
      var changed = false
      goals[stale[i]].modifyTypes { (t) in
        if t[.hasVariable] {
          let u = substitutions.reify(t, withVariables: .kept)
          changed = changed || (t != u)
          return u
        } else {
          return t
        }
      }

      if changed {
        log("- refresh \(goals[stale[i]])")
        fresh.append(stale.remove(at: i))
      }
    }
  }

  /// Logs a line of text in the standard output if `self.loggingIsEnabled` is `true`.
  private func log(_ line: @autoclosure () -> String) {
    if !loggingIsEnabled { return }
    print(String(repeating: "  ", count: indentation) + line())
  }

  /// Logs `outcome` in the standard output if `self.loggingIsEnabled` is `true`.
  private func log(outcome: Outcome?) {
    switch outcome {
    case nil:
      log("- defer")
    case .some(.success):
      log("- success")
    case .some(.failure):
      log("- failure")
    case .some(.product):
      log("- break")
    }
  }

  /// Logs `self`'s current state in the standard output if `self.loggingIsEnabled` is `true`.
  private func logState() {
    if !loggingIsEnabled { return }
    log("fresh:")
    for g in fresh {
      log("- \"\(goals[g])\"")
    }
    log("stale:")
    for g in stale {
      log("- \"\(goals[g])\"")
    }
  }

}

/// A closure reporting the diagnostics of a goal's failure into `d`, using `m` to reify types
/// and reading the outcome of other goals from `o`.
private typealias DiagnoseFailure = (
  _ d: inout DiagnosticSet,
  _ m: SubstitutionMap,
  _ o: OutcomeMap
) -> Void

/// The identity of a gaol in an instance of `ConstraintSystem`.
private typealias GoalIdentity = Int

/// A map from goal to its outcome.
private typealias OutcomeMap = [Outcome?]

/// The outcome of a goal.
private enum Outcome {

  /// The goal was solved.
  ///
  /// Information inferred from the goal has been stored in the solver's state.
  case success

  /// The goal was unsatisfiable.
  ///
  /// The goal was in conflict with the information inferred by the solver. The payload is a
  /// closure that generates a diagnostic of the conflict.
  case failure(DiagnoseFailure)

  /// The goal was broken into subordinate goal.
  ///
  /// The payload is a non-empty array of subordinate goals along with a closure that's used to
  /// generate a diagnostic in case one of the subordinate goals are unsatisfiable.
  case product([GoalIdentity], DiagnoseFailure)

  /// Returns the diagnosis constructor of `.failure` or `.product` payload.
  var diagnoseFailure: DiagnoseFailure? {
    switch self {
    case .success:
      return nil
    case .failure(let f):
      return f
    case .product(_, let f):
      return f
    }
  }

}

extension OutcomeMap {

  /// Returns whether the solving `g` succeeded or `.none` if outcome has been computed yet.
  fileprivate func succeeded(_ g: GoalIdentity) -> ThreeValuedBit {
    switch self[g] {
    case nil:
      return nil
    case .some(.success):
      return true
    case .some(.failure):
      return false
    case .some(.product(let s, _)):
      return s.reduce(true, { (r, k) in r && succeeded(k) })
    }
  }

}

/// A set of constraint system solutions resulting from the explorations of the different choices
/// of a disjunctive constraint.
private struct Explorations<T: DisjunctiveConstraintProtocol> {

  /// The solution of an exploration for a particular choice.
  typealias Element = (choice: T.Predicate, solution: Solution)

  /// The results of the exploration.
  private(set) var elements: [Element] = []

  /// The score of the solutions in this set.
  private(set) var score = Solution.Score.worst

  /// Creates an empty set.
  init() {}

  /// Inserts `newResult` into this set if its solution is better than or incomparable to any
  /// of the solutions currently in the set, ranking solutions with `rank`.
  mutating func insert(
    _ newResult: Element,
    rankingSolutionWith rank: (Solution, Solution) -> StrictPartialOrdering
  ) {
    // Rank solutions based on the name bindings they make. `s1` refines `s2` iff it has a better
    // score than `s2` or if it has the same score but makes at least one more specific binding
    // than `s2` and no binding less specific than `s2`.
    if newResult.solution.score > score { return }

    // Fast path: if the new solution has a better score, discard all others.
    if elements.isEmpty || (newResult.solution.score < score) {
      score = newResult.solution.score
      elements = [newResult]
      return
    }

    // Slow path: inspect how the new solution compares with the ones we have.
    var shouldInsert = false
    var i = 0
    while i < elements.count {
      switch rank(newResult.solution, elements[i].solution) {
      case .some(.equal):
        // The new solution is equal; discard it.
        return
      case .some(.descending):
        // The new solution is coarser; discard it unless it's better than another one.
        i += 1
      case .some(.ascending):
        // The new solution is finer; keep it and discard the old one.
        elements.remove(at: i)
        shouldInsert = true
      case nil:
        // The new solution is incomparable; keep it.
        i += 1
        shouldInsert = true
      }
    }

    if shouldInsert {
      elements.append(newResult)
    }
  }

}

extension Constraint {

  /// Returns whether `self` is heuristically simpler to solve than `rhs`.
  fileprivate func isSimpler(than rhs: any Constraint) -> Bool {
    if self is EqualityConstraint {
      return !(rhs is EqualityConstraint)
    } else if self.openVariables.isEmpty {
      return !rhs.openVariables.isEmpty
    } else if let l = self as? any DisjunctiveConstraintProtocol {
      if let r = rhs as? any DisjunctiveConstraintProtocol {
        if l.choices.count == r.choices.count {
          let x = l.choices.reduce(0, { $0 + $1.constraints.count })
          let y = r.choices.reduce(0, { $0 + $1.constraints.count })
          return x < y
        } else {
          return (l.choices.count < r.choices.count)
        }
      } else {
        return false
      }
    } else {
      return rhs is (any DisjunctiveConstraintProtocol)
    }
  }

}

/// Creates a constraint, suitable for type inference, requiring `subtype` to be a subtype of
/// `supertype`.
///
/// - Warning: For inference purposes, the result of this function must be used in place of a raw
///   `SubtypingConstraint` or the type checker will get stuck.
private func inferenceConstraint(
  _ subtype: AnyType,
  isSubtypeOf supertype: AnyType,
  origin: ConstraintOrigin
) -> Constraint {
  // If there aren't any type variable in neither `subtype` nor `supertype`, there's nothing to
  // infer and we can return a regular subtyping constraints.
  if !subtype[.hasVariable] && !supertype[.hasVariable] {
    return SubtypingConstraint(subtype, supertype, origin: origin)
  }

  // In other cases, we'll need two explorations. The first will unify `subtype` and `supertype`
  // and the other will try to infer them from the other constraints in the system.
  let alternative: Constraint
  if supertype.isLeaf {
    // If the supertype is a leaf, the subtype can only the same type or `Never`.
    alternative = EqualityConstraint(subtype, .never, origin: origin)
  } else {
    // Otherwise, the subtype can be any type upper-bounded by the supertype.
    alternative = SubtypingConstraint(subtype, supertype, strictly: true, origin: origin)
  }

  return DisjunctionConstraint(
    between: [
      .init(constraints: [EqualityConstraint(subtype, supertype, origin: origin)], penalties: 0),
      .init(constraints: [alternative], penalties: 1),
    ],
    origin: origin)
}
