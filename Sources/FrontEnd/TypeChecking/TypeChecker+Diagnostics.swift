extension Diagnostic {

  static func error(ambiguousDisjunctionAt site: SourceRange) -> Diagnostic {
    .error("ambiguous disjunction", at: site)
  }

  static func error(autoclosureExpectsEmptyEnvironment site: SourceRange, given: AnyType)
    -> Diagnostic
  {
    .error(
      "autoclosure parameter expects arrow type with no parameters (given type: \(given))",
      at: site)
  }

  static func error(
    binding a: BindingPattern.Introducer, requiresInitializerAt site: SourceRange
  ) -> Diagnostic {
    .error("declaration of \(a) binding requires an initializer", at: site)
  }

  static func error(invalidOptionPattern p: OptionPattern.ID, in ast: AST) -> Diagnostic {
    .error("optional pattern may only be used as a condition", at: ast[p].site)
  }

  static func error(circularRefinementAt site: SourceRange) -> Diagnostic {
    .error("circular trait refinement", at: site)
  }

  static func error(circularDependencyAt site: SourceRange) -> Diagnostic {
    .error("circular dependency", at: site)
  }

  static func error(cannotConstructRequirementSystem d: AnyDeclID, in ast: AST) -> Diagnostic {
    .error("requirement system too complex to build", at: ast.siteForDiagnostics(about: d))
  }

  static func error(cannotConstructTrait t: TraitType, at site: SourceRange) -> Diagnostic {
    .error("cannot construct an instance of trait '\(t)'; did you mean 'any \(t)'?", at: site)
  }

  static func error(cannotInferComplexReturnTypeAt site: SourceRange) -> Diagnostic {
    .error("cannot infer complex return type; add an explicit return type annotation", at: site)
  }

  static func error(conformanceToNonTraitType type: AnyType, at site: SourceRange) -> Diagnostic {
    .error("conformance to non-trait type '\(type)'", at: site)
  }

  static func error(
    redundantConformance c: Conformance,
    at site: SourceRange,
    alreadyDeclaredAt originalSite: SourceRange
  ) -> Diagnostic {
    .error(
      "redundant conformance of '\(c.model)' to trait '\(c.concept)'", at: site,
      notes: [
        .note("conformance already declared here", at: originalSite)
      ])
  }

  static func error(declarationRequiresBodyAt site: SourceRange) -> Diagnostic {
    .error("declaration requires a body", at: site)
  }

  static func error(duplicateCaptureNamed name: String, at site: SourceRange) -> Diagnostic {
    .error("duplicate capture name '\(name)'", at: site)
  }

  static func error(
    cannotCaptureOverloadedNameImplicitly name: SourceRepresentable<Name>
  ) -> Diagnostic {
    .error("cannot capture overloaded name '\(name.value)' implicitly", at: name.site)
  }

  static func error(duplicateOperatorNamed name: String, at site: SourceRange) -> Diagnostic {
    .error("duplicate operator declaration '\(name)'", at: site)
  }

  static func error(duplicateParameterNamed name: String, at site: SourceRange) -> Diagnostic {
    .error("duplicate parameter name '\(name)'", at: site)
  }

  static func error<T: ExprID>(typeExprDenotesValue e: T, in ast: AST) -> Diagnostic {
    let n = NameExpr.ID(e).map({ "'\(ast[$0].name.value)'" }) ?? "expression"
    return .error("expected type but \(n) denotes a value", at: ast[e].site)
  }

  static func error<S1: Sequence<String?>, S2: Sequence<String?>>(
    labels found: S1, incompatibleWith expected: S2, at site: SourceRange
  ) -> Diagnostic {
    .error(
      """
      incompatible labels: found '(\(Name.describe(labels: found)))', \
      expected '(\(Name.describe(labels: expected)))'
      """, at: site)
  }

  static func error(
    type l: AnyType, incompatibleWith r: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error("incompatible types '\(l)' and '\(r)'", at: site)
  }

  static func error(
    expected: AnyType, found: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error("expected type '\(expected)' but found '\(found)'", at: site)
  }

  static func error(invalidDestructuringOfType type: AnyType, at site: SourceRange) -> Diagnostic {
    .error("invalid destructuring of type '\(type)'", at: site)
  }

  static func error(invalidReferenceToSelfTypeAt site: SourceRange) -> Diagnostic {
    .error("reference to 'Self' outside of a type context", at: site)
  }

  static func error(invalidParameterType type: AnyType, at site: SourceRange) -> Diagnostic {
    .error("invalid parameter type '\(type)'", at: site)
  }

  static func error(missingReturnValueAt site: SourceRange) -> Diagnostic {
    .error("non-void function should return a value", at: site)
  }

  static func error(notATrait type: AnyType, at site: SourceRange) -> Diagnostic {
    .error("type '\(type)' is not a trait", at: site)
  }

  public static func error(
    _ type: AnyType, doesNotConformTo trait: TraitType, at site: SourceRange,
    because notes: DiagnosticSet = []
  ) -> Diagnostic {
    .error(
      "type '\(type)' does not conform to trait '\(trait)'", at: site,
      notes: Array(notes.elements))
  }

  static func error(tooManyExistentialBoundsAt site: SourceRange) -> Diagnostic {
    .error("existential generic type may have only one bound", at: site)
  }

  static func error(invalidExistentialInterface e: NameExpr.ID, in ast: AST) -> Diagnostic {
    .error("'\(ast[e].name.value)' is not a valid existential interface", at: ast[e].site)
  }

  static func error(
    invalidConformanceConstraintTo type: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error(
      """
      type '\(type)' in conformance constraint does not refers to a generic parameter or \
      associated type
      """, at: site)
  }

  static func error(
    invalidEqualityConstraintBetween l: AnyType, and r: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error(
      """
      neither type in equality constraint ('\(l)' or '\(r)') refers to a generic parameter or \
      associated type
      """, at: site)
  }

  static func error(unsatisfiedWhereClauseAt site: SourceRange) -> Diagnostic {
    .error("unsatisfied where clause", at: site)
  }

  static func error(notEnoughContextToInferArgumentsAt site: SourceRange) -> Diagnostic {
    .error("not enough contextual information to infer generic arguments", at: site)
  }

  static func error(
    notEnoughContextToResolveMember name: SourceRepresentable<Name>
  ) -> Diagnostic {
    .error("not enough contextual information to resolve member '\(name.value)'", at: name.site)
  }

  static func note(
    trait x: TraitType, requires r: NodeKind, named n: Name, typed t: AnyType, at site: SourceRange
  ) -> Diagnostic {
    let entity: String
    switch r {
    case FunctionDecl.self:
      entity = "function"
    case InitializerDecl.self:
      entity = "initializer"
    case MethodImpl.self:
      entity = "method"
    default:
      entity = "entity"
    }

    return .note("trait '\(x)' requires \(entity) '\(n)' with type '\(t)'", at: site)
  }

  static func note(
    trait x: TraitType, requiresAssociatedType n: String, at site: SourceRange
  ) -> Diagnostic {
    .note("trait '\(x)' requires associated type '\(n)'", at: site)
  }

  static func note(implementationMustBePublic d: AnyDeclID, in ast: AST) -> Diagnostic {
    .note(
      "implementation of trait requirement must be public",
      at: ast.siteForDiagnostics(about: d))
  }

  static func error(undefinedOperator name: String, at site: SourceRange) -> Diagnostic {
    .error("undefined operator '\(name)'", at: site)
  }

  static func warning(unusedResultOfType type: AnyType, at site: SourceRange) -> Diagnostic {
    .warning("unused result of type '\(type)'", at: site)
  }

  static func error(
    invalidGenericArgumentCountTo entity: SourceRepresentable<Name>, found: Int, expected: Int
  ) -> Diagnostic {
    if expected == 0 {
      return .error(
        "non-generic entity '\(entity.value)' has no generic parameters", at: entity.site)
    } else {
      return .error(
        """
        too \(found > expected ? "many" : "few") generic arguments to entity '\(entity.value)' \
        (found \(found), expected \(expected))
        """, at: entity.site)
    }
  }

  static func error(
    invalidBufferTypeArgumentCount found: Int, at site: SourceRange
  ) -> Diagnostic {
    .error("buffer type requires exactly one generic argument (found \(found))", at: site)
  }

  static func error(
    noViableCandidateToResolve entity: SourceRepresentable<Name>, notes: [Diagnostic]
  ) -> Diagnostic {
    .error("no viable candidate to resolve '\(entity.value)'", at: entity.site, notes: notes)
  }

  static func error(argumentToNonGenericType type: AnyType, at site: SourceRange) -> Diagnostic {
    .error("non-generic type '\(type)' has no generic parameters", at: site)
  }

  static func error(
    invalidBufferTypeExprArgumentCount e: SubscriptCallExpr.ID, in ast: AST
  ) -> Diagnostic {
    .error("buffer type expression requires exactly one argument", at: ast[ast[e].callee].site)
  }

  static func error(
    cannotCall type: AnyType, as entity: CallableEntity, at site: SourceRange
  ) -> Diagnostic {
    switch entity {
    case .function:
      return .error("cannot call value of type '\(type)' as a function", at: site)
    case .subscript:
      return .error("cannot call value of type '\(type)' as a subscript", at: site)
    }
  }

  static func error(
    undefinedName name: Name, in domain: AnyType? = nil, at site: SourceRange
  ) -> Diagnostic {
    if let domain = domain {
      return .error("type '\(domain)' has no member '\(name)'", at: site)
    } else {
      return .error("undefined name '\(name.stem)' in this scope", at: site)
    }
  }

  static func error(
    undefinedName name: Int, in domain: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error("type '\(domain)' has no member '\(name)'", at: site)
  }

  static func error(noContextToResolve name: Name, at site: SourceRange) -> Diagnostic {
    .error("reference to member '\(name)' cannot be resolved without context", at: site)
  }

  static func warning(unionTypeWithZeroElementsAt site: SourceRange) -> Diagnostic {
    .warning("empty union type is better expressed as 'Never'", at: site)
  }

  static func error(unionTypeWithOneElementAt site: SourceRange) -> Diagnostic {
    .error("union types should contain at least 2 elements", at: site)
  }

  static func error(valueInUnionTypeAt site: SourceRange) -> Diagnostic {
    .error("union types cannot contain values", at: site)
  }

  static func error(_ l: AnyType, isNotSubtypeOf r: AnyType, at site: SourceRange) -> Diagnostic {
    .error("'\(l)' is not subtype of '\(r)'", at: site)
  }

  static func error(
    cannotInitialize storageType: AnyType, with valueType: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error(
      "cannot initialize object of type '\(storageType)' with value of type '\(valueType)'",
      at: site)
  }

  static func error(
    _ l: AnyType, doesNotMatch pattern: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error("value of type '\(l)' does not match pattern '\(pattern)'", at: site)
  }

  static func error(
    _ subtype: AnyType, isNotStrictSubtypeOf supertype: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error("type '\(subtype)' is not strict subtype of '\(supertype)'", at: site)
  }

  static func error(
    ambiguousUse expr: NameExpr.ID, in ast: AST, candidates: [AnyDeclID] = []
  ) -> Diagnostic {
    .error(
      "ambiguous use of '\(ast[expr].name.value)'", at: ast[expr].site,
      notes: candidates.map { .note("candidate here", at: ast[$0].site) })
  }

  static func error(cannotExtend t: AnyType, at site: SourceRange) -> Diagnostic {
    .error("cannot extend type '\(t)'", at: site)
  }

  static func error(
    cannotPass t: AnyType, toParameter u: AnyType, at site: SourceRange
  ) -> Diagnostic {
    .error("cannot pass value of type '\(t)' to parameter '\(u)'", at: site)
  }

  static func error(
    conditionalHasMismatchingTypes t: [AnyType], at site: SourceRange
  ) -> Diagnostic {
    let s =
      (t.count == 2)
      ? "'\(t[0])' and '\(t[1])'"
      : t.map({ "'\($0)'" }).joined(separator: ", ")
    return .error("conditional expression has mismatching types \(s)", at: site)
  }

  static func error(noSuchModule n: String, at site: SourceRange) -> Diagnostic {
    .error("no such module '\(n)'", at: site)
  }

  static func error(invalidPointerConversionAt site: SourceRange) -> Diagnostic {
    .error("right operand of built-in pointer conversion must be a remote type", at: site)
  }

  static func error(
    invalidForLoopDomain m: AnyType, consuming: Bool, at site: SourceRange
  ) -> Diagnostic {
    if consuming {
      return .error(
        "consuming for loop requires '\(m)' to conform to 'Iterator'", at: site)
    } else {
      return .error(
        "non-consuming for loop requires '\(m)' to conform to 'Collection' or 'Iterator'", at: site)
    }
  }

  static func error(fallbackBranchCannotFallThroughAt site: SourceRange) -> Diagnostic {
    .error("fallback branch of conditional binding cannot fall through", at: site)
  }

  static func error(
    referenceTo d: SourceRepresentable<Name>, requires t: AnyType, conformsTo u: TraitType,
    dueToConstraintAt constraintSite: SourceRange
  ) -> Diagnostic {
    .error(
      "reference to '\(d.value)' requires that '\(t)' be conforming to '\(u)'",
      at: d.site,
      notes: [.note("constraint declared here", at: constraintSite)])
  }

  static func error(
    referenceTo d: SourceRepresentable<Name>, requires t: AnyType, equals u: AnyType,
    dueToConstraintAt constraintSite: SourceRange
  ) -> Diagnostic {
    .error(
      "reference to '\(d.value)' requires that '\(t)' be equal to '\(u)'",
      at: d.site,
      notes: [.note("constraint declared here", at: constraintSite)])
  }

  static func error(
    invalidReferenceToAssociatedType a: AssociatedTypeDecl.ID, at site: SourceRange, in ast: AST
  ) -> Diagnostic {
    .error(
      """
      associated type '\(ast[a].baseName)' can only be referred to with a concrete type or \
      generic parameter base
      """, at: site)
  }

  static func error(
    invalidReferenceToInaccessible ds: [AnyDeclID], named n: SourceRepresentable<Name>, in ast: AST
  ) -> Diagnostic {
    .error(
      "'\(n.value)' is inaccessible due to its protection level", at: n.site,
      notes: ds.map { (d) in .note("'\(n.value)' declared here", at: ast[d].site) })
  }

  static func error(recursiveDefinition d: AnyDeclID, in ast: AST) -> Diagnostic {
    .error("definition recursively depends on itself", at: ast.siteForDiagnostics(about: d))
  }

  static func error(referenceToSibling e: NameExpr.ID, in ast: AST) -> Diagnostic {
    .error("default value cannot refer to a sibling capture or parameter", at: ast[e].site)
  }

  static func warning(needlessImport d: ImportDecl.ID, in ast: AST) -> Diagnostic {
    let s = ast[d].identifier
    return .warning("needless import: source file is part of '\(s.value)'", at: s.site)
  }

}
