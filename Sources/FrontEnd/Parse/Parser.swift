import Durian
import Utils

/// # Notes:
///
/// Be careful when writing rules that start with an optional symbol that may be recognized at
/// the beginning of the following construct. A naive combinator may not be able to backtrack.
/// For example:
///
///     let p0 = maybe(foo.and(bar)).and(ham)
///     let p1 = foo.and(bar).or(ham)
///
/// Both `p0` and `p1` will fail to recognize inputs recognized by `ham` if `foo` can recognize
/// the same prefix, as the latter will throw a committing failure it applies `bar` rather than
/// backtracking. A correct definition is:
///
///     let p2 = attempt(foo.and(bar)).or(foo)

/// A namespace for the routines of Hylo's parser.
public enum Parser {

  /// Parses the contents of `input` as a translation unit, registering the identities of newly
  /// formed ASTs in space `k` and reporting errors to `diagnostics`.
  ///
  /// - Throws: Diagnostics if syntax errors were encountered.
  public static func parse(
    _ input: SourceFile,
    inNodeSpace k: Int,
    in ast: inout AST,
    diagnostics: inout DiagnosticSet,
    profileWith profiler: ProfilingMeasurements?
  ) throws -> TranslationUnit.ID {
    // Temporarily stash the AST and diagnostics in the parser state, avoiding CoW costs
    var state = ParserState(
      ast: ast, space: k, lexer: Lexer(tokenizing: input, profileWith: profiler),
      reportingDiagnosticsTo: diagnostics)
    defer { diagnostics = state.diagnostics }
    diagnostics = DiagnosticSet()

    // Parse the input.
    var members: [AnyDeclID] = []

    // start time measurement if needed
    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.Parser)
    defer { probe?.stop() }

    while let head = state.peek() {
      // Ignore semicolons.
      if state.take(.semi) != nil { continue }

      // Attempt to parse a member.
      let startIndex = state.currentIndex
      do {
        if let member = try parseDecl(in: &state) {
          members.append(member)
          continue
        }
      } catch let error as DiagnosticSet {
        state.diagnostics.formUnion(error.elements)
        continue
      } catch let error {
        state.diagnostics.insert(
          Diagnostic(
            level: .error,
            message: "\(type(of: error)): \(error)",
            site: state.lexer.sourceCode.range(startIndex..<state.currentIndex)))
        continue
      }

      // Attempt to recover.
      _ = state.take()
      switch head.kind {
      case .unterminatedBlockComment:
        // Nothing to parse after an unterminated block comment.
        state.diagnostics.insert(
          .error(unterminatedCommentStartingAt: head.site.start))
        break

      case .unterminatedString:
        // Nothing to parse after an unterminated string.
        state.diagnostics.insert(
          .error(unterminatedStringStartingAt: head.site.start))
        break

      default:
        state.diagnostics.insert(.error(unexpectedToken: head))

        // Attempt to recover at the next new line.
        while let next = state.peek() {
          if state.hasNewline(before: next) { break }
          _ = state.take()
        }
      }
    }

    // Make sure the entire input was consumed.
    assert(state.peek() == nil, "expected EOF")

    let translation = state.insert(
      TranslationUnit(
        decls: members,
        site: input.range(input.text.startIndex..<input.text.endIndex)))

    try state.diagnostics.throwOnError()
    ast = state.ast
    return translation
  }

  /// Fails the parsing of the expected construct with the given diagnostic.
  private static func fail(_ d: Diagnostic) throws -> Never {
    throw [d] as DiagnosticSet
  }

  /// Fails the parsing of the expected construct with the given diagnostics.
  private static func fail<C: Collection<Diagnostic>>(_ ds: C) throws -> Never {
    throw DiagnosticSet(ds)
  }

  // MARK: Declarations

  /// Parses a declaration prologue in `state` and then calls `continuation`.
  static func parseDeclPrologue<R>(
    in state: inout ParserState,
    then continuation: (_ prologue: DeclPrologue, _ state: inout ParserState) throws -> R?
  ) throws -> R? {
    guard let startIndex = state.peek()?.site.startIndex else { return nil }

    // Parse attributes.
    let attributes = try parseAttributeList(in: &state) ?? []
    var prologueIsEmpty = attributes.isEmpty

    // Parse modifiers.
    var accessModifiers: Set<SourceRepresentable<AccessModifier>> = []
    var memberModifiers: Set<SourceRepresentable<MemberModifier>> = []
    while true {
      if let access = try Parser.accessModifier.parse(&state) {
        prologueIsEmpty = false

        // Catch access modifiers declared after member modifiers.
        if let member = memberModifiers.first {
          state.diagnostics.insert(
            .error(
              memberModifier: member,
              appearsBeforeAccessModifier: access))
        }

        // Catch inconsistent access modifiers.
        else if let p = accessModifiers.first, p != access {
          state.diagnostics.insert(
            .error(
              inconsistentAccessModifiers: access,
              appearsAfterPreviousAccessModifier: p))
        }

        // Catch duplicate access modifiers.
        else if !accessModifiers.insert(access).inserted {
          state.diagnostics.insert(.error(duplicateAccessModifier: access))
        }

        // Look for the next modifier.
        continue
      }

      if let member = try Parser.memberModifier.parse(&state) {
        prologueIsEmpty = false

        // Catch member modifiers declared at non-type scope.
        if !state.isAtTypeScope {
          state.diagnostics.insert(.error(unexpectedMemberModifier: member))
        }

        // Catch duplicate member modifiers.
        else if !memberModifiers.insert(member).inserted {
          state.diagnostics.insert(.error(duplicateMemberModifier: member))
        }

        // Look for the next modifier.
        continue
      }

      break
    }

    // Apply the continuation.
    let prologue = DeclPrologue(
      isEmpty: prologueIsEmpty,
      startIndex: startIndex,
      attributes: attributes,
      accessModifiers: accessModifiers,
      memberModifiers: memberModifiers)
    return try continuation(prologue, &state)
  }

  /// Parses a declaration in `state`.
  static func parseDecl(in state: inout ParserState) throws -> AnyDeclID? {
    func continuation(
      prologue: DeclPrologue,
      state: inout ParserState
    ) throws -> AnyDeclID? {
      // Look ahead to select the appropriate declaration parser.
      switch state.peek()?.kind {
      case .let, .inout, .var, .sink:
        return try parseBindingDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .fun, .infix, .postfix, .prefix:
        return try parseFunctionOrMethodDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .`init`:
        return try parseInitDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .subscript:
        return try parseSubscriptDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .property:
        return try parsePropertyDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .namespace:
        return try parseNamespaceDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .trait:
        return try parseTraitDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .type:
        if state.isAtTraitScope {
          return try parseAssociatedTypeDecl(withPrologue: prologue, in: &state)
            .map(AnyDeclID.init)
        } else {
          return try parseProductTypeDecl(withPrologue: prologue, in: &state)
            .map(AnyDeclID.init)
        }

      case .typealias:
        return try parseTypeAliasDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .conformance:
        return try parseConformanceDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .extension:
        return try parseExtensionDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .import:
        return try parseImportDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .operator:
        return try parseOperatorDecl(withPrologue: prologue, in: &state)
          .map(AnyDeclID.init)

      case .name:
        let introducer = state.lexer.sourceCode[state.peek()!.site]
        if introducer == "value" && state.isAtTypeScope {
          // Note: associated values are parsed at any type scope to produce better diagnostics
          // when they are not at trait scope.
          return try parseAssociatedValueDecl(withPrologue: prologue, in: &state)
            .map(AnyDeclID.init)
        }
        if introducer == "memberwise" && state.isAtTypeScope {
          return try parseMemberwiseInitDecl(withPrologue: prologue, in: &state)
            .map(AnyDeclID.init)
        }

      default:
        break
      }

      if prologue.isEmpty {
        return nil
      } else {
        try fail(.error(expected: "declaration", at: state.currentLocation))
      }
    }

    // Note: this return statement must follow the declaration of `continuation` to work around
    // an apparent bug in swiftc. See: https://github.com/apple/swift/issues/62136
    return try parseDeclPrologue(in: &state, then: continuation)
  }

  /// Parses the body of a type declaration, adding `context` to `state.contexts` while parsing
  /// each member declaration.
  ///
  /// - Note: The function never returns a soft failure. It will throw if it can't parse the left
  ///   brace of the body, even if it didn't consume any token from the stream.
  ///
  /// - Parameters:
  ///   - state: A mutable projection of the parser's state.
  ///   - context: The parser context in which members should be parsed.
  private static func parseTypeDeclBody(
    in state: inout ParserState,
    wrappedIn context: ParserState.Context
  ) throws -> [AnyDeclID] {
    // Parse the left delimiter.
    let opener = try state.expect("'{'", using: { $0.take(.lBrace) })

    // Push the context.
    state.contexts.append(context)
    defer { state.contexts.removeLast() }

    // Parse the members.
    var members: [AnyDeclID] = []
    while true {
      // Ignore semicolons.
      if state.take(.semi) != nil { continue }

      // Exit if we find the right delimiter.
      if state.take(.rBrace) != nil { break }

      // Attempt to parse a member.
      do {
        if let member = try parseDecl(in: &state) {
          members.append(member)
          continue
        }
      } catch let error as DiagnosticSet {
        state.diagnostics.formUnion(error.elements)
        continue
      }

      // Nothing was consumed. Skip the next token or, if we reached EOF, diagnose a missing right
      // delimiter and exit.
      guard let head = state.take() else {
        state.diagnostics.insert(
          .error(
            expected: "'}'",
            at: state.currentLocation,
            notes: [.note("to match this '{'", at: opener.site)]
          ))
        break
      }

      // Diagnose the error.
      state.diagnostics.insert(.error(expected: "declaration", at: head.site.start))

      // Skip tokens until we find a right delimiter or the start of another declaration.
      state.skip(while: { (next) in !next.mayBeginDecl && (next.kind != .rBrace) })
    }

    return members
  }

  /// Parses an instance of `AssociatedTypeDecl`.
  static func parseAssociatedTypeDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> AssociatedTypeDecl.ID? {
    // Parse the parts of the declaration.
    let parser =
      (take(.type).and(take(.name))
        .and(maybe(conformanceList))
        .and(maybe(whereClause))
        .and(maybe(take(.assign).and(expr).second)))
    guard let parts = try parser.parse(&state) else { return nil }

    // Associated type declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Associated type declarations shall not have modifiers.
    if !prologue.accessModifiers.isEmpty {
      try fail(prologue.accessModifiers.map(Diagnostic.error(unexpectedAccessModifier:)))
    }
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `AssociatedTypeDecl`.
    return state.insert(
      AssociatedTypeDecl(
        introducerSite: parts.0.0.0.0.site,
        identifier: state.token(parts.0.0.0.1),
        conformances: parts.0.0.1 ?? [],
        whereClause: parts.0.1,
        defaultValue: parts.1,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `AssociatedValueDecl`.
  static func parseAssociatedValueDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> AssociatedValueDecl.ID? {
    // Parse the parts of the declaration.
    let parser =
      (take(nameTokenWithValue: "value").and(take(.name))
        .and(maybe(whereClause))
        .and(maybe(take(.assign).and(expr).second)))
    guard let parts = try parser.parse(&state) else { return nil }

    // Associated value declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Associated value declarations shall not have modifiers.
    if !prologue.accessModifiers.isEmpty {
      try fail(prologue.accessModifiers.map(Diagnostic.error(unexpectedAccessModifier:)))
    }
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `AssociatedValueDecl`.
    return state.insert(
      AssociatedValueDecl(
        introducerSite: parts.0.0.0.site,
        identifier: state.token(parts.0.0.1),
        whereClause: parts.0.1,
        defaultValue: parts.1,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses a declaration of bindings.
  private static func parseBindingDecl(in state: inout ParserState) throws -> BindingDecl.ID? {
    try parseDeclPrologue(in: &state, then: parseBindingDecl(withPrologue:in:))
  }

  /// Parses a declaration of bindings prefixed by the given (already parsed) `prologue`.
  static func parseBindingDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> BindingDecl.ID? {
    guard let pattern = try parseBindingPattern(in: &state) else { return nil }
    let initializer = try parseDefaultValue(in: &state)

    // Create a new `BindingDecl`.
    assert(prologue.memberModifiers.count <= 1)
    return state.insert(
      BindingDecl(
        attributes: prologue.attributes,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        memberModifier: prologue.memberModifiers.first,
        pattern: pattern,
        initializer: initializer,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `ConformanceDecl`.
  static func parseConformanceDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> ConformanceDecl.ID? {
    // Parse the parts of the declaration.
    let parser =
      (take(.conformance).and(expr)
        .and(conformanceList)
        .and(maybe(whereClause))
        .and(Apply({ (s) in try parseTypeDeclBody(in: &s, wrappedIn: .extensionBody) })))
    guard let parts = try parser.parse(&state) else { return nil }

    // Conformance declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Conformance declarations shall not have member modifiers.
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `ConformanceDecl`.
    return state.insert(
      ConformanceDecl(
        introducerSite: parts.0.0.0.0.site,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        subject: parts.0.0.0.1,
        conformances: parts.0.0.1,
        whereClause: parts.0.1,
        members: parts.1,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `ExtensionDecl`.
  static func parseExtensionDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> ExtensionDecl.ID? {
    // Parse the parts of the declaration.
    let parser =
      (take(.extension).and(expr)
        .and(maybe(whereClause))
        .and(Apply({ (s) in try parseTypeDeclBody(in: &s, wrappedIn: .extensionBody) })))
    guard let parts = try parser.parse(&state) else { return nil }

    // Extension declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Extension declarations shall not have member modifiers.
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `ExtensionDecl`.
    return state.insert(
      ExtensionDecl(
        introducerSite: parts.0.0.0.site,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        subject: parts.0.0.1,
        whereClause: parts.0.1,
        members: parts.1,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `FunctionDecl` or `MethodDecl`.
  static func parseFunctionOrMethodDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> AnyDeclID? {
    // Parse the signature of the function or method.
    guard let head = try parseFunctionDeclHead(in: &state) else { return nil }
    let signature = try state.expect("function signature", using: parseFunctionDeclSignature(in:))

    // Parse the body of the function or method.
    let body = try functionOrMethodDeclBody.parse(&state)

    // Apply the continuation corresponding to the body we just parsed.
    switch body {
    case .method(let impls):
      return try AnyDeclID(
        buildMethodDecl(
          prologue: prologue,
          head: head,
          signature: signature,
          impls: impls,
          in: &state))

    case .function(let body):
      return try AnyDeclID(
        buildFunctionDecl(
          prologue: prologue,
          head: head,
          signature: signature,
          body: body,
          in: &state))

    case nil:
      return try AnyDeclID(
        buildFunctionDecl(
          prologue: prologue,
          head: head,
          signature: signature,
          body: nil,
          in: &state))
    }
  }

  /// Builds a new instance of `FunctionDecl` from its parsed parts.
  private static func buildFunctionDecl(
    prologue: DeclPrologue,
    head: FunctionDeclHead,
    signature: FunctionDeclSignature,
    body: FunctionBody?,
    in state: inout ParserState
  ) throws -> FunctionDecl.ID {
    // Non-static member function declarations require an implicit receiver parameter.
    let receiver: ParameterDecl.ID?
    if state.isAtTypeScope && !prologue.isStatic {
      receiver = state.insert(
        synthesized: ParameterDecl(
          identifier: SourceRepresentable(value: "self", range: head.introducerSite),
          site: head.introducerSite))
    } else {
      receiver = nil
    }

    // Create a new `FunctionDecl`.
    assert(prologue.memberModifiers.count <= 1)
    return state.insert(
      FunctionDecl(
        introducerSite: head.introducerSite,
        attributes: prologue.attributes,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        memberModifier: prologue.memberModifiers.first,
        receiverEffect: signature.receiverEffect,
        notation: head.notation,
        identifier: head.stem,
        genericClause: head.genericClause,
        explicitCaptures: head.captures,
        parameters: signature.parameters,
        receiver: receiver,
        output: signature.output,
        body: body,
        site: state.range(from: prologue.startIndex)))
  }

  /// Builds a new instance of `Method` from its parsed parts.
  private static func buildMethodDecl(
    prologue: DeclPrologue,
    head: FunctionDeclHead,
    signature: FunctionDeclSignature,
    impls: [MethodImpl.ID],
    in state: inout ParserState
  ) throws -> MethodDecl.ID {
    // Method declarations cannot be static.
    if let modifier = prologue.memberModifiers.first(where: { (m) in m.value == .static }) {
      try fail(.error(unexpectedMemberModifier: modifier))
    }

    // Method declarations cannot have a receiver effect.
    if let effect = signature.receiverEffect {
      try fail(.error(unexpectedEffect: effect))
    }

    // Method declarations cannot have captures.
    if let capture = head.captures.first {
      try fail(.error(unexpectedCapture: state.ast[state.ast[capture].pattern]))
    }

    // Create a new `MethodDecl`.
    return state.insert(
      MethodDecl(
        introducerSite: head.introducerSite,
        attributes: prologue.attributes,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        notation: head.notation,
        identifier: head.stem,
        genericClause: head.genericClause,
        parameters: signature.parameters,
        output: signature.output,
        impls: impls,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `ImportDecl`.
  static func parseImportDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> ImportDecl.ID? {
    // Parse the parts of the declaration.
    let parser = (take(.import).and(take(.name)))
    guard let parts = try parser.parse(&state) else { return nil }

    // Import declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Import declarations shall not have modifiers.
    if !prologue.accessModifiers.isEmpty {
      try fail(prologue.accessModifiers.map(Diagnostic.error(unexpectedAccessModifier:)))
    }
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `ImportDecl`.
    return state.insert(
      ImportDecl(
        introducerSite: parts.0.site,
        identifier: state.token(parts.1),
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `InitializerDecl`.
  static func parseInitDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> InitializerDecl.ID? {
    // Parse the signature of the initializer.
    guard let introducer = state.take(.`init`) else { return nil }
    let genericClause = try genericClause.parse(&state)
    let parameters = try state.expect("function signature", using: parseParameterList(in:))

    // Parse the body of the initializer.
    let body = try initDeclBody.parse(&state)

    // Init declarations cannot be static.
    if let modifier = prologue.memberModifiers.first(where: { (m) in m.value == .static }) {
      try fail(.error(unexpectedMemberModifier: modifier))
    }

    // Init declarations require an implicit receiver parameter.
    let receiver = state.insert(
      synthesized: ParameterDecl(
        identifier: SourceRepresentable(value: "self", range: introducer.site),
        site: introducer.site))

    // Create a new `InitializerDecl`.
    assert(prologue.memberModifiers.isEmpty)
    return state.insert(
      InitializerDecl(
        introducer: SourceRepresentable(value: .`init`, range: introducer.site),
        attributes: prologue.attributes,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        genericClause: genericClause,
        parameters: parameters,
        receiver: receiver,
        body: body,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `InitializerDecl`.
  static func parseMemberwiseInitDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> InitializerDecl.ID? {
    // Parse the introducer.
    guard let a = state.take(nameTokenWithValue: "memberwise") else { return nil }
    let b = try state.expect("'init'", using: { $0.take(.`init`) })
    let introducerSite = a.site.extended(toCover: b.site)

    // Init declarations cannot be static.
    if let modifier = prologue.memberModifiers.first(where: { (m) in m.value == .static }) {
      try fail(.error(unexpectedMemberModifier: modifier))
    }

    // Init declarations require an implicit receiver parameter.
    let receiver = state.insert(
      synthesized: ParameterDecl(
        identifier: SourceRepresentable(value: "self", range: introducerSite),
        site: introducerSite))

    // Create a new `InitializerDecl`.
    return state.insert(
      InitializerDecl(
        introducer: SourceRepresentable(value: .memberwiseInit, range: introducerSite),
        attributes: prologue.attributes,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        genericClause: nil,
        parameters: [],
        receiver: receiver,
        body: nil,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `NamespaceDecl`.
  static func parseNamespaceDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> NamespaceDecl.ID? {
    // Parse the parts of the declaration.
    let parser =
      (take(.namespace).and(take(.name))
        .and(Apply({ (s) in try parseTypeDeclBody(in: &s, wrappedIn: .namespaceBody) })))
    guard let parts = try parser.parse(&state) else { return nil }

    // Namespace declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Namespace declarations shall not have member modifiers.
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `NamespaceDecl`.
    return state.insert(
      NamespaceDecl(
        introducerSite: parts.0.0.site,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        identifier: state.token(parts.0.1),
        members: parts.1,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `OperatorDecl`.
  static func parseOperatorDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> OperatorDecl.ID? {
    // Parse the parts of the declaration.
    let parser =
      (take(.operator).and(operatorNotation)
        .and(operatorIdentifier)
        .and(maybe(take(.colon).and(precedenceGroup).second)))
    guard let parts = try parser.parse(&state) else { return nil }

    // Operator declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Operator declarations shall not have member modifiers.
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `OperatorDecl`.
    return state.insert(
      OperatorDecl(
        introducerSite: parts.0.0.0.site,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        notation: parts.0.0.1,
        name: parts.0.1,
        precedenceGroup: parts.1,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `SubscriptDecl` representing a property declaration.
  static func parsePropertyDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> SubscriptDecl.ID? {
    guard let (head, signature) = try propertyDeclHead.and(propertyDeclSignature).parse(&state)
    else { return nil }

    let isNonStatic = state.isAtTypeScope && !prologue.isStatic
    let impls = try state.expect(
      "'{'",
      using: { (s) in try parseSubscriptDeclBody(in: &s, asNonStaticMember: isNonStatic) })

    // Create a new `SubscriptDecl`.
    assert(prologue.memberModifiers.count <= 1)
    return state.insert(
      SubscriptDecl(
        introducer: head.introducer,
        attributes: prologue.attributes,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        memberModifier: prologue.memberModifiers.first,
        identifier: head.stem,
        genericClause: nil,
        explicitCaptures: [],
        parameters: [],
        output: signature,
        impls: impls,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `SubscriptDecl`.
  static func parseSubscriptDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> SubscriptDecl.ID? {
    // Parse the signature of the subscript.
    guard let head = try subscriptDeclHead.parse(&state) else { return nil }
    let signature = try state.expect(
      "subscript signature",
      using: parseSubscriptDeclSignature(in:))

    let isNonStatic = state.isAtTypeScope && !prologue.isStatic
    let impls = try state.expect(
      "'{'",
      using: { (s) in try parseSubscriptDeclBody(in: &s, asNonStaticMember: isNonStatic) })

    // Create a new `SubscriptDecl`.
    assert(prologue.memberModifiers.count <= 1)
    return state.insert(
      SubscriptDecl(
        introducer: head.introducer,
        attributes: prologue.attributes,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        memberModifier: prologue.memberModifiers.first,
        identifier: head.stem,
        genericClause: head.genericClause,
        explicitCaptures: head.captures,
        parameters: signature.parameters,
        output: signature.output,
        impls: impls,
        site: state.range(from: prologue.startIndex)))
  }

  static func parseSubscriptDeclBody(
    in state: inout ParserState,
    asNonStaticMember isNonStaticMember: Bool
  ) throws -> [SubscriptImpl.ID]? {
    // Push the context.
    state.contexts.append(.subscriptBody)
    defer { state.contexts.removeLast() }

    // Parse the left delimiter.
    let backup = state.backup()
    if state.take(.lBrace) == nil { return nil }

    // Parse the subscript implementations.
    var impls: [SubscriptImpl.ID] = []
    var introducers = AccessEffectSet()
    while true {
      // Exit if we find the right delimiter.
      if state.take(.rBrace) != nil { break }

      // Parse an implementation.
      if let (introducer, body) = try subscriptImpl.parse(&state) {
        let impl = try buildSubscriptImpl(
          in: &state,
          introducedBy: introducer,
          body: body,
          asNonStaticMember: isNonStaticMember)
        impls.append(impl)

        if !introducers.insert(introducer.value).inserted {
          state.diagnostics.insert(.error(duplicateImplementationIntroducer: introducer))
        }
      } else {
        state.diagnostics.insert(.error(expected: .rBrace, at: state.currentLocation))
        break
      }
    }

    if !impls.isEmpty { return impls }

    // Fall back to a single body.
    state.restore(from: backup)
    guard let body = try functionBody.parse(&state) else { return nil }
    let i = try buildSubscriptImpl(
      in: &state,
      introducedBy: SourceRepresentable(
        value: .let,
        range: state.lexer.sourceCode.emptyRange(at: state.ast[body.base].site.startIndex)),
      body: body,
      asNonStaticMember: isNonStaticMember)
    return [i]
  }

  /// Inserts a subscript having the given `introducer` and `body` into `state.ast` and returns its
  /// ID.
  ///
  /// - Parameters:
  ///   - introducer: The introducer of the declaration, or `nil` if it is implicit. In that case,
  ///     it is synthesized as `let`.
  ///   - body: The body of the declaration, or `nil` if that body should must be synthesized or
  ///     if the declaration denotes a trait requirement.
  /// - Requires: if `introducer` is `nil`, body is non-`nil`.
  private static func buildSubscriptImpl(
    in state: inout ParserState,
    introducedBy introducer: SourceRepresentable<AccessEffect>,
    body: FunctionBody?,
    asNonStaticMember isNonStaticMember: Bool
  ) throws -> SubscriptImpl.ID {
    // Non-static member subscript declarations require an implicit receiver parameter.
    let receiver: ParameterDecl.ID?
    if isNonStaticMember {
      receiver = state.insert(
        synthesized: ParameterDecl(
          identifier: SourceRepresentable(value: "self", range: introducer.site),
          site: introducer.site))
    } else {
      receiver = nil
    }

    let site: SourceRange
    if let n = body?.base {
      site = introducer.site.extended(toCover: state.ast[n].site)
    } else {
      site = introducer.site
    }

    // Create a new `SubscriptImpl`.
    return state.insert(
      SubscriptImpl(
        introducer: introducer,
        receiver: receiver,
        body: body,
        site: site))
  }

  /// Parses an instance of `TraitDecl`.
  static func parseTraitDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> TraitDecl.ID? {
    guard let introducer = state.take(.trait) else { return nil }

    // Parse the parts of the declaration.
    let name = try state.expect("identifier", using: { $0.take(.name) })
    let bounds = try conformanceList.parse(&state) ?? []
    var members = try state.expect(
      "trait body",
      using: { (s) in
        try parseTypeDeclBody(in: &s, wrappedIn: .traitBody)
      })

    // Trait declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Synthesize the `Self` parameter of the trait.
    let selfParameterDecl = state.insert(
      GenericParameterDecl(
        introducer: SourceRepresentable(value: .type, range: introducer.site),
        identifier: SourceRepresentable(value: "Self", range: name.site),
        site: name.site))
    members.append(AnyDeclID(selfParameterDecl))

    // Create a new `TraitDecl`.
    return state.insert(
      TraitDecl(
        introducerSite: introducer.site,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        identifier: state.token(name),
        bounds: bounds,
        members: members,
        selfParameterDecl: selfParameterDecl,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `ProductTypeDecl`.
  static func parseProductTypeDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> ProductTypeDecl.ID? {
    // Parse the parts of the declaration.
    let parser =
      (take(.type).and(take(.name))
        .and(maybe(genericClause))
        .and(maybe(conformanceList))
        .and(Apply({ (s) in try parseTypeDeclBody(in: &s, wrappedIn: .productBody) })))
    guard let parts = try parser.parse(&state) else { return nil }

    // Product type declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Product type declarations shall not have member modifiers.
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `ProductTypeDecl`.
    return state.insert(
      ProductTypeDecl(
        introducerSite: parts.0.0.0.0.site,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        identifier: state.token(parts.0.0.0.1),
        genericClause: parts.0.0.1,
        conformances: parts.0.1 ?? [],
        members: parts.1,
        site: state.range(from: prologue.startIndex)))
  }

  /// Parses an instance of `TypeAliasDecl`.
  static func parseTypeAliasDecl(
    withPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) throws -> TypeAliasDecl.ID? {
    // Parse the parts of the declaration.
    guard let introducer = state.take(.typealias) else { return nil }

    let n = try state.token(state.expect("identifier", using: { $0.take(.name) }))
    let g = try genericClause.parse(&state)
    guard state.take(.assign) != nil else {
      state.skipUntilNextDecl()
      try fail(.error(declarationRequiresDefinitionAt: .empty(at: state.currentLocation)))
    }
    let e = try state.expect("type expression", using: parseExpr(in:))

    // Type alias declarations shall not have attributes.
    if !prologue.attributes.isEmpty {
      try fail(prologue.attributes.map(Diagnostic.error(unexpectedAttribute:)))
    }

    // Type alias declarations shall not have member modifiers.
    if !prologue.memberModifiers.isEmpty {
      try fail(prologue.memberModifiers.map(Diagnostic.error(unexpectedMemberModifier:)))
    }

    // Create a new `TypeAliasDecl`.
    return state.insert(
      TypeAliasDecl(
        introducerSite: introducer.site,
        accessModifier: declAccessModifier(ofDeclPrologue: prologue, in: &state),
        identifier: n,
        genericClause: g,
        aliasedType: e,
        site: state.range(from: prologue.startIndex)))
  }

  /// Returns the access modifier in `prologue` if in contains one, or synthesizes an implicit one.
  private static func declAccessModifier(
    ofDeclPrologue prologue: DeclPrologue,
    in state: inout ParserState
  ) -> SourceRepresentable<AccessModifier> {
    // Declarations are private by default.
    assert(prologue.accessModifiers.count <= 1)
    return prologue.accessModifiers.first
      ?? SourceRepresentable(
        value: .private, range: state.lexer.sourceCode.emptyRange(at: prologue.startIndex))
  }

  static func parseFunctionDeclHead(
    in state: inout ParserState
  ) throws -> FunctionDeclHead? {
    guard let introducer = state.take(.fun) else { return nil }

    let stem: SourceRepresentable<Identifier>
    let notation: SourceRepresentable<OperatorNotation>?

    if let n = try operatorNotation.parse(&state) {
      stem = try state.expect("operator", using: operatorIdentifier)
      notation = n
    } else {
      stem = try state.token(state.expect("identifier", using: { $0.take(.name) }))
      notation = nil
    }

    let genericClause = try genericClause.parse(&state)
    let captures = try captureList.parse(&state) ?? []

    return FunctionDeclHead(
      introducerSite: introducer.site,
      stem: stem,
      notation: notation,
      genericClause: genericClause,
      captures: captures)
  }

  static func parseFunctionDeclSignature(
    in state: inout ParserState
  ) throws -> FunctionDeclSignature? {
    guard let parameters = try parseParameterList(in: &state) else { return nil }

    let effect = try receiverEffect.parse(&state)

    let output: AnyExprID?
    if state.take(.arrow) != nil {
      output = try state.expect("type expression", using: parseExpr(in:))
    } else {
      output = nil
    }

    return FunctionDeclSignature(parameters: parameters, receiverEffect: effect, output: output)
  }

  private static let functionOrMethodDeclBody = TryCatch(
    trying:
      methodDeclBody
      .map({ (state, body) -> FunctionOrMethodDeclBody in .method(body) }),
    orCatchingAndApplying:
      functionBody
      .map({ (state, body) -> FunctionOrMethodDeclBody in .function(body) })
  )

  static let functionBody = inContext(
    .functionBody,
    apply: TryCatch(
      trying: take(.lBrace).and(expr).and(take(.rBrace))
        .map({ (state, tree) -> FunctionBody in .expr(tree.0.1) }),
      orCatchingAndApplying:
        braceStmt
        .map({ (state, id) -> FunctionBody in .block(id) })
    ))

  static let methodDeclBody =
    (take(.lBrace).and(methodImpl+).and(take(.rBrace))
      .map({ (state, tree) -> [MethodImpl.ID] in
        var introducers = AccessEffectSet()
        for implID in tree.0.1 {
          let introducer = state.ast[implID].introducer
          if !introducers.insert(introducer.value).inserted {
            state.diagnostics.insert(.error(duplicateImplementationIntroducer: introducer))
          }
        }
        return tree.0.1
      }))

  static let methodImpl =
    (implIntroducer.and(maybe(functionBody))
      .map({ (state, tree) -> MethodImpl.ID in
        let receiver = state.insert(
          ParameterDecl(
            identifier: SourceRepresentable(value: "self", range: tree.0.site),
            site: tree.0.site))
        return state.insert(
          MethodImpl(
            introducer: tree.0,
            receiver: receiver,
            body: tree.1,
            site: tree.0.site.extended(upTo: state.currentIndex)))
      }))

  static let implIntroducer = translate([
    .let: AccessEffect.let,
    .inout: AccessEffect.inout,
    .set: AccessEffect.set,
    .sink: AccessEffect.sink,
  ])

  static let initDeclBody = inContext(.functionBody, apply: braceStmt)

  static let operatorIdentifier =
    (Apply<ParserState, SourceRepresentable<Identifier>>({ (state) in
      state.takeOperator()
    }))

  static let operatorNotation = translate([
    .infix: OperatorNotation.infix,
    .prefix: OperatorNotation.prefix,
    .postfix: OperatorNotation.postfix,
  ])

  static let precedenceGroup = ContextualKeyword<PrecedenceGroup>()

  static let propertyDeclHead =
    (take(.property).and(take(.name))
      .map({ (state, tree) -> PropertyDeclHead in
        PropertyDeclHead(
          introducer: SourceRepresentable(value: .property, range: tree.0.site),
          stem: state.token(tree.1))
      }))

  static let propertyDeclSignature = (take(.colon).and(expr).second)

  static let subscriptDeclHead =
    (take(.subscript).and(maybe(take(.name))).and(maybe(genericClause)).and(maybe(captureList))
      .map({ (state, tree) -> SubscriptDeclHead in
        SubscriptDeclHead(
          introducer: SourceRepresentable(value: .subscript, range: tree.0.0.0.site),
          stem: tree.0.0.1.map({ state.token($0) }),
          genericClause: tree.0.1,
          captures: tree.1 ?? [])
      }))

  static func parseSubscriptDeclSignature(
    in state: inout ParserState
  ) throws -> SubscriptDeclSignature? {
    guard let parameters = try parseParameterList(in: &state) else { return nil }

    _ = try state.expect("':'", using: { $0.take(.colon) })
    let output = try state.expect("type expression", using: parseExpr(in:))

    return SubscriptDeclSignature(parameters: parameters, output: output)
  }

  static let subscriptImpl = (implIntroducer.and(maybe(functionBody)))

  /// Parses a parameter declaration.
  static func parseParameterDecl(in state: inout ParserState) throws -> ParameterDecl.ID? {
    guard let interface = try parseParameterInterface(in: &state) else { return nil }

    let annotation = try parseAscription(in: &state, parseParameterTypeExpr(in:))
    let defaultValue = try parseDefaultValue(in: &state)

    let isImplicit = interface.implicitMarker != nil
    if isImplicit {
      if let e = state.ast[annotation]?.convention, e.value != .let {
        state.diagnostics.insert(.error(illegalAccessModifierForImplicitParameter: e))
      }
    }

    return state.insert(
      ParameterDecl(
        label: interface.label,
        identifier: interface.name,
        annotation: annotation,
        defaultValue: defaultValue,
        isImplicit: isImplicit,
        site: state.range(
          from: interface.label?.site.startIndex ?? interface.name.site.startIndex)))
  }

  /// Parses the (optional) label and name of a parameter declaration.
  static func parseParameterInterface(
    in state: inout ParserState
  ) throws -> ParameterInterface? {
    guard let i = try parseParameterNameAndLabel(in: &state) else { return nil }
    let q = state.takePostfixQuestionMark()
    return ParameterInterface(label: i.label, name: i.name, implicitMarker: q)
  }

  /// Parses the (optional) label and name of a parameter declaration.
  private static func parseParameterNameAndLabel(
    in state: inout ParserState
  ) throws -> (label: SourceRepresentable<Identifier>?, name: SourceRepresentable<Identifier>)? {
    guard let labelCandidate = state.take(if: { $0.isLabel || $0.kind == .under }) else {
      return nil
    }

    // Assume the first token is a label and attempt to parse a name.
    if let nameCandidate = state.take(.name) {
      if labelCandidate.kind == .under {
        // case `_ name`
        return (label: nil, name: state.token(nameCandidate))
      } else {
        // case `label name`
        return (label: state.token(labelCandidate), name: state.token(nameCandidate))
      }
    }

    // Assume the first token is the name.
    if labelCandidate.kind == .name {
      // case `<no-label> name`
      let name = state.token(labelCandidate)
      return (label: name, name: name)
    }

    try fail(.error(expected: "parameter name", at: labelCandidate.site.start))
  }

  static let memberModifier =
    (take(.static)
      .map({ (_, token) -> SourceRepresentable<MemberModifier> in
        SourceRepresentable(value: .static, range: token.site)
      }))

  static let accessModifier = translate([
    .internal: AccessModifier.internal,
    .private: AccessModifier.private,
    .public: AccessModifier.public,
  ])

  static let captureList = Apply(parseCaptureList(in:))

  /// Parses a capture list.
  private static func parseCaptureList(in state: inout ParserState) throws -> [BindingDecl.ID]? {
    try parseList(in: &state, with: captureListSpecification)
  }

  /// Parses an explicit capture declaration.
  private static func parseCaptureDecl(in state: inout ParserState) throws -> BindingDecl.ID? {
    try parseBindingDecl(in: &state)
  }

  /// The specification of a capture list, for use in `parseList(in:with:)`.
  private static let captureListSpecification = DelimitedCommaSeparatedList(
    openerKind: .lBrack,
    closerKind: .rBrack,
    closerDescription: "]",
    elementParser: Apply(parseCaptureDecl(in:)))

  static let genericClause =
    (take(.lAngle).and(genericParameterListContents).and(maybe(whereClause)).and(take(.rAngle))
      .map({ (state, tree) -> SourceRepresentable<GenericClause> in
        return SourceRepresentable(
          value: GenericClause(parameters: tree.0.0.1, whereClause: tree.0.1),
          range: tree.0.0.0.site.extended(upTo: state.currentIndex))
      }))

  static let genericParameterListContents =
    (genericParameter.and(zeroOrMany(take(.comma).and(genericParameter).second))
      .map({ (_, tree) -> [GenericParameterDecl.ID] in [tree.0] + tree.1 }))

  static let genericParameter = Apply(parseGenericParameterDecl(in:))

  private static func parseGenericParameterDecl(
    in state: inout ParserState
  ) throws -> GenericParameterDecl.ID? {
    let i = parseGenericParameterIntroducer(in: &state)

    guard let n = state.take(.name) else {
      if i == nil {
        return nil
      } else {
        try fail(.error(expected: "identifier", at: state.currentLocation))
      }
    }

    let a = try parseAscription(in: &state, boundComposition.parse(_:))
    let v = try parseDefaultValue(in: &state)

    return state.insert(
      GenericParameterDecl(
        introducer: i,
        identifier: state.token(n),
        conformances: a ?? [],
        defaultValue: v,
        site: (i?.site ?? n.site).extended(upTo: state.currentIndex)))
  }

  private static func parseGenericParameterIntroducer(
    in state: inout ParserState
  ) -> SourceRepresentable<GenericParameterDecl.Introducer>? {
    (state.take(.type) ?? state.take(nameTokenWithValue: "value")).map { (t) in
      if t.kind == .type {
        return .init(value: .type, range: t.site)
      } else {
        return .init(value: .value, range: t.site)
      }
    }
  }

  static let conformanceList =
    (take(.colon).and(nameTypeExpr).and(zeroOrMany(take(.comma).and(nameTypeExpr).second))
      .map({ (state, tree) -> [NameExpr.ID] in [tree.0.1] + tree.1 }))

  /// Parses a binding initializer or a parameter default value.
  private static func parseDefaultValue(in state: inout ParserState) throws -> AnyExprID? {
    if state.take(.assign) != nil {
      return try state.expect("expression", using: parseExpr(in:))
    } else {
      return nil
    }
  }

  /// Parses a colon and returns the result of `ascription` applied on `state`.
  private static func parseAscription<T>(
    in state: inout ParserState, _ ascription: (inout ParserState) throws -> T?
  ) throws -> T? {
    if state.take(.colon) != nil {
      return try state.expect("type expression", using: ascription)
    } else {
      return nil
    }
  }

  // MARK: Expressions

  static let expr = Apply(parseExpr(in:))

  /// Parses an expression in `state`.
  static func parseExpr(in state: inout ParserState) throws -> AnyExprID? {
    // Parse an expression.
    guard var lhs = try parsePrefixExpr(in: &state) else { return nil }

    // Append infix tails.
    while state.hasLeadingWhitespace {
      guard
        let e = try
          (appendingCastTail(to: lhs, in: &state) ?? appendingInfixTail(to: lhs, in: &state))
      else { break }
      lhs = e
    }

    return lhs
  }

  /// If the next token is a cast operator, parses an expression and returns a `CastExpr` appending
  /// it to `lhs`; returns `nil` otherwise.
  private static func appendingCastTail(
    to lhs: AnyExprID,
    in state: inout ParserState
  ) throws -> AnyExprID? {
    guard let infixOperator = state.take(.cast) else { return nil }
    if !state.hasLeadingWhitespace {
      state.diagnostics.insert(.error(infixOperatorRequiresWhitespacesAt: infixOperator.site))
    }

    let castKind: CastExpr.Direction
    switch state.lexer.sourceCode[infixOperator.site] {
    case "as":
      castKind = .up
    case "as!":
      castKind = .down
    case "as*":
      castKind = .pointerConversion
    default:
      unreachable()
    }

    let rhs = try state.expect("type expression", using: parseExpr(in:))
    return AnyExprID(
      state.insert(
        CastExpr(
          introducerSite: infixOperator.site,
          left: lhs,
          right: rhs,
          direction: castKind,
          site: state.ast[lhs].site.extended(upTo: state.currentIndex))))
  }

  /// Parses pairs of infix operators and prefix expressions and, if one or more pairs were parsed,
  /// returns a `SequenceExpr` appending them to `lhs`; returns `nil` otherwise.
  private static func appendingInfixTail(
    to lhs: AnyExprID,
    in state: inout ParserState
  ) throws -> AnyExprID? {
    var tail: [SequenceExpr.TailElement] = []

    while true {
      let backup = state.backup()

      // Look for the next operator.
      guard let operatorStem = state.takeOperator() else { break }

      if !state.hasLeadingWhitespace {
        // If there isn't any leading whitespace before the next expression but the operator is on
        // a different line, we may be looking at the start of a prefix expression.
        let rangeBefore = state.ast[lhs].site.endIndex..<operatorStem.site.startIndex
        if state.lexer.sourceCode.text[rangeBefore].contains(where: { $0.isNewline }) {
          state.restore(from: backup)
          break
        }

        // Otherwise, complain about missing whitespaces.
        state.diagnostics.insert(.error(infixOperatorRequiresWhitespacesAt: operatorStem.site))
      }

      // If we can't parse an operand, the tail is empty.
      guard let operand = try parsePrefixExpr(in: &state) else {
        state.restore(from: backup)
        return nil
      }

      let `operator` = state.insert(
        NameExpr(
          domain: .operand,
          name: SourceRepresentable(
            value: Name(stem: operatorStem.value, notation: .infix), range: operatorStem.site),
          site: operatorStem.site))
      tail.append(SequenceExpr.TailElement(operator: `operator`, operand: operand))
    }

    // Nothing to transform if the tail is empty.
    if tail.isEmpty { return nil }

    return AnyExprID(
      state.insert(
        SequenceExpr(
          head: lhs,
          tail: tail,
          site: state.ast[lhs].site.extended(upTo: state.currentIndex))))
  }

  private static func parsePrefixExpr(in state: inout ParserState) throws -> AnyExprID? {
    // Attempt to parse a prefix operator.
    if state.isNext(satisfying: { $0.isPrefixOperatorHead }) {
      let op = state.takeOperator()!

      // Parse an operand.
      let isSeparated = state.hasLeadingWhitespace
      let operand = try state.expect("expression", using: parsePostfixExpr(in:))

      // There must be no space before the next expression.
      if isSeparated {
        state.diagnostics.insert(.error(separatedPrefixOperatorAt: op.site))
      }

      let callee = state.insert(
        NameExpr(
          domain: .explicit(operand),
          name: SourceRepresentable(
            value: Name(stem: op.value, notation: .prefix),
            range: op.site),
          site: state.range(from: op.site.startIndex)))

      let call = state.insert(
        FunctionCallExpr(
          callee: AnyExprID(callee),
          arguments: [],
          site: state.ast[callee].site))
      return AnyExprID(call)
    }

    // Fall back to a postfix expression.
    return try parsePostfixExpr(in: &state)
  }

  private static func parsePostfixExpr(in state: inout ParserState) throws -> AnyExprID? {
    // Parse an operand.
    guard let operand = try parseCompoundExpr(in: &state) else { return nil }

    // Return the parser expression if it's followed by a whitespace.
    if state.hasLeadingWhitespace { return operand }

    // Parse a postfix operator.
    if state.isNext(satisfying: { $0.isPostfixOperatorHead }) {
      let op = state.takeOperator()!

      let callee = state.insert(
        NameExpr(
          domain: .explicit(operand),
          name: SourceRepresentable(
            value: Name(stem: op.value, notation: .postfix),
            range: op.site),
          site: state.range(from: state.ast[operand].site.startIndex)))

      let call = state.insert(
        FunctionCallExpr(
          callee: AnyExprID(callee),
          arguments: [],
          site: state.ast[callee].site))
      return AnyExprID(call)
    } else {
      return operand
    }
  }

  private static func parseCompoundExpr(in state: inout ParserState) throws -> AnyExprID? {
    guard var head = try parseCompoundExprHead(in: &state) else { return nil }
    let headOrigin = state.ast[head].site

    // Parse the components to append to the base expression.
    while true {
      if let e = try appendingNameComponent(to: head, in: &state) {
        head = e
        continue
      }

      // Handle conformance lens expressions.
      if state.take(.twoColons) != nil {
        // Note: We're using the `parsePrimaryExpr(in:)` parser rather that `parseExpr(in:)` so
        // that `A::P.T` is parsed as `(A::P).T`.
        let lens = try state.expect("expression", using: parsePrimaryExpr(in:))
        let expr = state.insert(
          ConformanceLensExpr(
            subject: head,
            lens: lens,
            site: state.range(from: headOrigin.startIndex)))
        head = AnyExprID(expr)
        continue
      }

      // Exit if there's a new line before the next token.
      guard let next = state.peek(), !state.hasNewline(before: next) else { break }

      // Handle function calls.
      if next.kind == .lParen {
        let arguments = try parseFunctionCallArgumentList(in: &state)!
        let expr = state.insert(
          FunctionCallExpr(
            callee: head,
            arguments: arguments,
            site: state.range(from: headOrigin.startIndex)))
        head = AnyExprID(expr)
        continue
      }

      // Handle subscript calls.
      if next.kind == .lBrack {
        let arguments = try parseSubscriptCallArgumentList(in: &state)!
        let expr = state.insert(
          SubscriptCallExpr(
            callee: head,
            arguments: arguments,
            site: state.range(from: headOrigin.startIndex)))
        head = AnyExprID(expr)
        continue
      }

      break
    }

    return head
  }

  private static func parseCompoundExprHead(in state: inout ParserState) throws -> AnyExprID? {
    guard let op = state.take(.ampersand) else {
      return try parsePrimaryExpr(in: &state)
    }

    let isSeparated = state.hasLeadingWhitespace
    var operand = try state.expect("expression", using: parsePrimaryExpr(in:))
    if isSeparated {
      state.diagnostics.insert(.error(separatedMutationMarkerAt: op.site))
    }

    while let e = try appendingNameComponent(to: operand, in: &state) { operand = e }
    return AnyExprID(
      state.insert(
        InoutExpr(
          operatorSite: op.site,
          subject: operand,
          site: state.range(from: op.site.startIndex))))
  }

  /// If the next token is a dot, parses a tuple or name components, and returns respectively a
  /// `TupleMemberExpr` or `NameExpr` appending it to `head`; returns `nil` otherwise.
  private static func appendingNameComponent(
    to head: AnyExprID,
    in state: inout ParserState
  ) throws -> AnyExprID? {
    guard state.take(.dot) != nil else { return nil }

    if let index = state.takeMemberIndex() {
      let e = state.insert(
        TupleMemberExpr(
          tuple: head,
          index: index,
          site: state.range(from: state.ast[head].site.startIndex)))
      return AnyExprID(e)
    }

    if let component = try parseNameExprComponent(in: &state) {
      let e = state.insert(
        NameExpr(
          domain: .explicit(head),
          name: component.name,
          arguments: component.arguments,
          site: state.range(from: state.ast[head].site.startIndex)))
      return AnyExprID(e)
    }

    try fail(.error(expected: "member name", at: state.currentLocation))
  }

  private static func parsePrimaryExpr(in state: inout ParserState) throws -> AnyExprID? {
    guard let head = state.peek() else { return nil }

    switch head.kind {
    case .bool:
      // Boolean literal.
      _ = state.take()
      let expr = state.insert(
        BooleanLiteralExpr(
          value: state.lexer.sourceCode[head.site] == "true",
          site: head.site))
      return AnyExprID(expr)

    case .int:
      // Integer or Float literal.
      return try parseIntegerOrFloatLiteralExpr(in: &state)

    case .string:
      // String literal.
      _ = state.take()
      let expr = state.insert(
        StringLiteralExpr(
          value: String(state.lexer.sourceCode[head.site].dropFirst().dropLast()),
          site: head.site))
      return AnyExprID(expr)

    case .under:
      // Wildcard expression.
      _ = state.take()
      let expr = state.insert(WildcardExpr(site: head.site))
      return AnyExprID(expr)

    case .any:
      // Existential type expression.
      return try parseExistentialTypeExpr(in: &state).map(AnyExprID.init)

    case .dot:
      // Implicit member reference.
      return try parseImplicitMemberDeclRefExpr(in: &state).map(AnyExprID.init)

    case .fun:
      // Lambda expression.
      return try parseLambdaExpr(in: &state).map(AnyExprID.init)

    case .if:
      // Conditional expression.
      return try parseConditionalExpr(in: &state).map(AnyExprID.init)

    case .match:
      // Match expression.
      return try parseMatchExpr(in: &state).map(AnyExprID.init)

    case .name:
      // Primary declaration reference.
      return try parsePrimaryDeclRefExpr(in: &state).map(AnyExprID.init)

    case .pragmaLiteral:
      // Pragma literal.
      return try parsePragmaLiteralExpr(in: &state).map(AnyExprID.init)

    case .remote:
      // Remote type expression.
      return try parseRemoteExpr(in: &state).map(AnyExprID.init)

    case .spawn:
      // Spawn expression.
      return try parseSpawnExpr(in: &state).map(AnyExprID.init)

    case .lBrace:
      // Tuple type expression.
      return try parseTupleTypeExpr(in: &state).map(AnyExprID.init)

    case .lParen:
      // A left parenthesis may start a type erased arrow type expression (e.g., `() -> T`), a
      // tuple expression (e.g., `(1, 2)`), or any parenthesized expression.
      return try parseArrowTypeOrTupleExpr(in: &state)

    case .lBrack:
      // A left bracket may start an arrow type expression (e.g., `[any Copyable]() -> T`), a
      // compound literal expression (e.g., `[x, y]`), or a capture (e.g., `[let x]`).
      return try parseArrowTypeOrBracketedExpr(in: &state)

    default:
      return nil
    }
  }

  /// Parses an integer or float literal expression from `state`.
  private static func parseIntegerOrFloatLiteralExpr(
    in state: inout ParserState
  ) throws -> AnyExprID? {
    guard let integer = state.take(.int) else { return nil }

    if let e = parseFloatLiteralExpr(after: integer, in: &state) {
      return AnyExprID(e)
    }

    let e = state.insert(
      IntegerLiteralExpr(
        value: state.lexer.sourceCode[integer.site].filter({ $0 != "_" }),
        site: integer.site))
    return AnyExprID(e)
  }

  /// Parses a float literal expression from `state`, assuming it has the given `integerPart`.
  private static func parseFloatLiteralExpr(
    after integerPart: Token, in state: inout ParserState
  ) -> FloatLiteralExpr.ID? {
    let i = state.currentIndex
    _ = state.take(.dot, .int) != nil
    _ = state.take(.exponent)

    if state.currentIndex == i { return nil }

    let s = integerPart.site.extended(upTo: state.currentIndex)
    return state.insert(
      FloatLiteralExpr(value: state.lexer.sourceCode[s].filter({ $0 != "_" }), site: s))
  }

  private static func parseExistentialTypeExpr(
    in state: inout ParserState
  ) throws -> ExistentialTypeExpr.ID? {
    // Parse the introducer.
    guard let introducer = state.take(.any) else { return nil }

    // Parse the parts of the expression.
    let traits = try state.expect("trait composition", using: boundComposition)
    let clause = try whereClause.parse(&state)

    return state.insert(
      ExistentialTypeExpr(
        introducerSite: introducer.site,
        traits: traits,
        whereClause: clause,
        site: introducer.site.extended(
          toCover: clause?.site ?? state.ast[traits.last!].site)))
  }

  private static func parsePrimaryDeclRefExpr(
    in state: inout ParserState
  ) throws -> NameExpr.ID? {
    // Parse the name component.
    let component = try state.expect("identifier", using: parseNameExprComponent(in:))

    return state.insert(
      NameExpr(
        domain: .none,
        name: component.name,
        arguments: component.arguments,
        site: component.site))
  }

  /// Parses a pragma literal from `state`.
  private static func parsePragmaLiteralExpr(
    in state: inout ParserState
  ) throws -> PragmaLiteralExpr.ID? {
    guard let t = state.take(.pragmaLiteral) else { return nil }

    let result: PragmaLiteralExpr.Kind
    switch state.lexer.sourceCode[t.site].dropFirst() {
    case "file":
      result = .file
    case "line":
      result = .line
    case let n:
      try fail(.error(unknownPragma: n, at: t.site))
    }

    return state.insert(PragmaLiteralExpr(result, at: t.site))
  }

  private static func parseImplicitMemberDeclRefExpr(
    in state: inout ParserState
  ) throws -> NameExpr.ID? {
    // Parse the leading dot.
    guard let head = state.take(.dot) else { return nil }

    // Parse the name component.
    let component = try state.expect("identifier", using: parseNameExprComponent(in:))

    return state.insert(
      NameExpr(
        domain: .implicit,
        name: component.name,
        arguments: component.arguments,
        site: state.range(from: head.site.startIndex)))
  }

  private static func parseNameExprComponent(
    in state: inout ParserState
  ) throws -> NameExprComponent? {
    // Parse the name of the component.
    guard let name = try parseEntityName(in: &state) else { return nil }

    // If the next token is a left angle bracket without any leading whitespace, parse a static
    // argument list.
    let arguments: [LabeledArgument]
    if !state.hasLeadingWhitespace && state.isNext(.lAngle) {
      arguments = try state.expect("static argument list", using: parseStaticArgumentList(in:))
    } else {
      arguments = []
    }

    return NameExprComponent(
      site: name.site.extended(upTo: state.currentIndex),
      name: name,
      arguments: arguments)
  }

  private static func parseArgument(in state: inout ParserState) throws -> LabeledArgument? {
    let backup = state.backup()

    // Parse a labeled argument.
    if let label = state.take(if: { $0.isLabel }) {
      if state.take(.colon) != nil {
        if let value = try parseExpr(in: &state) {
          return LabeledArgument(label: state.token(label), value: value)
        }
      }
    }

    // Backtrack and parse an unlabeled argument.
    state.restore(from: backup)
    if let value = try parseExpr(in: &state) {
      return LabeledArgument(label: nil, value: value)
    }

    return nil
  }

  private static func parseEntityName(
    in state: inout ParserState
  ) throws -> SourceRepresentable<Name>? {
    try parseFunctionEntityName(in: &state) ?? parseOperatorEntityName(in: &state)
  }

  private static func parseFunctionEntityName(
    in state: inout ParserState
  ) throws -> SourceRepresentable<Name>? {
    // Parse the stem identifier.
    guard let identifier = state.take(if: { t in t.isOf(kind: [.name, .under]) }) else {
      return nil
    }

    // Parse the labels, if any.
    var labels: [String?] = []
    if !state.hasLeadingWhitespace && (state.peek()?.kind == .lParen) {
      let backup = state.backup()
      _ = state.take()
      var closeParenFound = false
      defer {
        // Backtrack if we didn't find a closing parenthesis or if there are no labels. That will
        // let the argument-list parser pickup after the identifier to either catch a parse error
        // in the former case (no closing parenthesis) or parse an empty argument list in the
        // latter (no labels).
        // Note: `foo()` is *not* a valid name, it's a function call.
        if !closeParenFound || labels.isEmpty {
          labels.removeAll()
          state.restore(from: backup)
        }
      }

      while !state.hasLeadingWhitespace {
        if state.take(.under) != nil {
          labels.append(nil)
        } else if let label = state.take(if: { $0.isLabel }) {
          labels.append(String(state.lexer.sourceCode[label.site]))
        } else {
          break
        }

        if state.takeWithoutSkippingWhitespace(.colon) == nil {
          break
        }

        if state.takeWithoutSkippingWhitespace(.rParen) != nil {
          closeParenFound = true
          break
        }
      }
    }

    // Parse the method introducer, if any.
    let introducer: SourceRepresentable<AccessEffect>?
    if state.peek()?.kind == .dot {
      let backup = state.backup()
      _ = state.take()
      if let i = try implIntroducer.parse(&state) {
        introducer = i
      } else {
        state.restore(from: backup)
        introducer = nil
      }
    } else {
      introducer = nil
    }

    return SourceRepresentable(
      value: Name(
        stem: String(state.lexer.sourceCode[identifier.site]),
        labels: labels,
        introducer: introducer?.value),
      range: state.range(from: identifier.site.startIndex))
  }

  private static func parseOperatorEntityName(
    in state: inout ParserState
  ) throws -> SourceRepresentable<Name>? {
    // Parse the operator notation.
    guard let notation = state.take(if: { t in t.isOf(kind: [.infix, .prefix, .postfix]) }) else {
      return nil
    }

    // The notation must be immediately followed by an operator identifier.
    if state.hasLeadingWhitespace {
      try fail(.error(expected: "operator", at: state.currentLocation))
    }
    let identifier = try state.expect("operator", using: { $0.takeOperator() })

    return SourceRepresentable(
      value: Name(stem: identifier.value, notation: OperatorNotation(notation)!),
      range: state.range(from: identifier.site.startIndex))
  }

  private static func parseLambdaExpr(in state: inout ParserState) throws -> LambdaExpr.ID? {
    // Parse the introducer.
    guard let introducer = state.take(.fun) else { return nil }

    // Parse the parts of the expression.
    let explicitCaptures = try captureList.parse(&state)
    let signature = try state.expect("signature", using: parseFunctionDeclSignature(in:))
    let body = try state.expect("function body", using: lambdaBody)

    let decl = state.insert(
      FunctionDecl(
        introducerSite: introducer.site,
        accessModifier: SourceRepresentable(value: .private, range: introducer.site),
        receiverEffect: signature.receiverEffect,
        explicitCaptures: explicitCaptures ?? [],
        parameters: signature.parameters,
        output: signature.output,
        body: body,
        isInExprContext: true,
        site: state.range(from: introducer.site.startIndex)))
    return state.insert(
      LambdaExpr(decl: decl, site: state.ast[decl].site))
  }

  private static let lambdaBody = inContext(
    .functionBody,
    apply: TryCatch(
      trying: take(.lBrace).and(expr).and(take(.rBrace))
        .map({ (state, tree) -> FunctionBody in .expr(tree.0.1) }),
      orCatchingAndApplying:
        braceStmt
        .map({ (state, id) -> FunctionBody in .block(id) })
    ))

  /// Parses a conditional expression.
  private static func parseConditionalExpr(
    in state: inout ParserState
  ) throws -> ConditionalExpr.ID? {
    guard let introducer = state.take(.if) else { return nil }

    let c = try state.expect("condition", using: conditionalClause)
    let a = try state.expect("'{'", using: parseBracedExpr(in:))
    let elseIntroducer = try state.expect("'else'", using: { $0.take(.else) })
    let b: AnyExprID = try state.expect(
      "expression",
      using: { (s) in
        try parseConditionalExpr(in: &s).map(AnyExprID.init(_:)) ?? parseBracedExpr(in: &s)
      })

    let elseClause = Introduced(b, at: elseIntroducer.site)

    return state.insert(
      ConditionalExpr(
        introducerSite: introducer.site, condition: c, success: a, failure: elseClause,
        site: state.range(from: introducer.site.startIndex)))
  }

  /// Parses a single expression enclosed in curly braces.
  private static func parseBracedExpr(
    in state: inout ParserState
  ) throws -> AnyExprID? {
    guard let opener = state.take(.lBrace) else { return nil }
    let body = try state.expect("expression", using: parseExpr(in:))
    if state.take(.rBrace) == nil {
      state.diagnostics.insert(.error(expected: "}", matching: opener, in: state))
    }
    return body
  }

  private static func parseMatchExpr(in state: inout ParserState) throws -> MatchExpr.ID? {
    // Parse the introducer.
    guard let introducer = state.take(.match) else { return nil }

    // Parse the parts of the expression.
    let subject = try state.expect("subject", using: parseExpr(in:))
    let cases = try state.expect("match body", using: parseMatchBody(in:))

    return state.insert(
      MatchExpr(
        introducerSite: introducer.site,
        subject: subject,
        cases: cases,
        site: state.range(from: introducer.site.startIndex)))
  }

  private static func parseMatchBody(in state: inout ParserState) throws -> [MatchCase.ID]? {
    guard let opener = state.take(.lBrace) else { return nil }

    var result: [MatchCase.ID] = []
    while let c = try parseMatchCase(in: &state) {
      result.append(c)
    }

    if state.take(.rBrace) == nil {
      state.diagnostics.insert(.error(expected: "}", matching: opener, in: state))
    }
    return result
  }

  private static func parseMatchCase(in state: inout ParserState) throws -> MatchCase.ID? {
    guard let pattern = try parsePattern(in: &state) else { return nil }

    // Parse the condition, if any.
    let condition: AnyExprID?
    if state.take(.where) != nil {
      condition = try state.expect("expression", using: parseExpr(in:))
    } else {
      condition = nil
    }

    // Parse the body.
    let body = try state.expect("case body", using: parseMatchCaseBody(in:))

    return state.insert(
      MatchCase(
        pattern: pattern,
        condition: condition,
        body: body,
        site: state.range(from: state.ast[pattern].site.startIndex)))
  }

  private static func parseMatchCaseBody(in state: inout ParserState) throws -> MatchCase.Body? {
    let backup = state.backup()

    // Attempt to parse an expression.
    if let opener = state.take(.lBrace) {
      do {
        if let e = try parseExpr(in: &state) {
          if state.take(.rBrace) == nil {
            state.diagnostics.insert(.error(expected: "}", matching: opener, in: state))
          }
          return .expr(e)
        }
      } catch {}
      state.restore(from: backup)
    }

    guard let s = try braceStmt.parse(&state) else { return nil }
    return .block(s)
  }

  private static func parseRemoteExpr(
    in state: inout ParserState
  ) throws -> RemoteTypeExpr.ID? {
    guard let introducer = state.take(.remote) else { return nil }

    let convention = try state.expect("access effect", using: accessEffect)
    let operand = try state.expect("expression", using: parseExpr(in:))

    return state.insert(
      RemoteTypeExpr(
        introducerSite: introducer.site,
        convention: convention,
        operand: operand,
        site: state.range(from: introducer.site.startIndex)))
  }

  private static func parseSpawnExpr(in state: inout ParserState) throws -> SpawnExpr.ID? {
    // Parse the introducer.
    guard let introducer = state.take(.spawn) else { return nil }

    // Parse the parts of the expression.
    let explicitCaptures = try captureList.parse(&state) ?? []
    let effect = try receiverEffect.parse(&state)

    let output: AnyExprID?
    let body: FunctionBody
    if state.take(.arrow) != nil {
      output = try state.expect("expression", using: parseExpr(in:))
      body = try state.expect("function body", using: lambdaBody)
    } else {
      output = nil
      body = try .expr(state.expect("expression", using: parseExpr(in:)))
    }

    let decl = state.insert(
      FunctionDecl(
        introducerSite: introducer.site,
        accessModifier: SourceRepresentable(value: .private, range: introducer.site),
        receiverEffect: effect,
        explicitCaptures: explicitCaptures,
        output: output,
        body: body,
        isInExprContext: true,
        site: state.range(from: introducer.site.startIndex)))
    return state.insert(
      SpawnExpr(decl: decl, site: state.ast[decl].site))
  }

  private static func parseArrowTypeOrTupleExpr(
    in state: inout ParserState
  ) throws -> AnyExprID? {
    // Expect a left parenthesis.
    guard
      let opener = state.peek(),
      opener.kind == .lParen
    else { return nil }

    // Assume we're parsing an arrow type expression until we reach the point where we should
    // consume a right arrow. Commit to that choice only if there's one.
    let backup = state.backup()

    // Parse the parameters or backtrack and parse a tuple expression.
    let parameters: [ArrowTypeExpr.Parameter]
    do {
      parameters = try parseArrowParameterList(in: &state)!
    } catch {
      state.restore(from: backup)
      return try parseTupleOrParenthesizedExpr(in: &state)
    }

    // Parse the remainder of the type expression.
    let effect = try receiverEffect.parse(&state)

    guard state.take(.arrow) != nil else {
      // If we didn't parse any effect and the parameter list is empty, assume we parsed an empty
      // tuple. Otherwise, backtrack and parse a tuple expression.
      if (effect == nil) && parameters.isEmpty {
        let expr = state.insert(
          TupleExpr(
            elements: [],
            site: state.range(from: opener.site.startIndex)))
        return AnyExprID(expr)
      }

      state.restore(from: backup)
      return try parseTupleOrParenthesizedExpr(in: &state)
    }

    let output = try state.expect("type expression", using: parseExpr(in:))

    let expr = state.insert(
      ArrowTypeExpr(
        receiverEffect: effect,
        environment: nil,
        parameters: parameters,
        output: output,
        site: state.range(from: opener.site.startIndex)))
    return AnyExprID(expr)
  }

  private static func parseArrowTypeOrBracketedExpr(
    in state: inout ParserState
  ) throws -> AnyExprID? {
    // There are 4 kinds of expressions starting with a left bracket: arrow types, buffers, maps,
    // and captures. We can commit to a capture if the token following the opening bracket is an
    // access modifier. Otherwise, we can assume we're parsing an arrow type until the point where
    // we should consume an effect or a right arrow.
    let backup = state.backup()

    guard let opener = state.take(.lBrack) else { return nil }
    if let k = try accessEffect.parse(&state) {
      let s = try state.expect("expression", using: parseExpr(in:))
      _ = try state.expect("']'", using: { $0.take(.rBrack) })
      let e = state.insert(
        CaptureExpr(access: k, source: s, site: state.range(from: opener.site.startIndex)))
      return AnyExprID(e)
    }

    let environment = try parseExpr(in: &state)
    if state.take(.rBrack) == nil {
      state.restore(from: backup)
      return try parseCompoundLiteral(in: &state)
    }

    // We're here because we parsed either `[]` or `[e]`, where `e` is an arbitrary expression. If
    // we don't find an opening parenthesis next, we can assume we've parsed a buffer literal.
    if !state.isNext(.lParen) {
      let expr = state.insert(
        BufferLiteralExpr(
          elements: environment != nil ? [environment!] : [],
          site: state.range(from: opener.site.startIndex)))
      return AnyExprID(expr)
    }

    // Parse the parameters or backtrack and parse a compound literal.
    let parameters: [ArrowTypeExpr.Parameter]
    do {
      parameters = try parseArrowParameterList(in: &state)!
    } catch {
      state.restore(from: backup)
      return try parseCompoundLiteral(in: &state)
    }

    // Parse the remainder of the type expression.
    let effect = try receiverEffect.parse(&state)
    if state.take(.arrow) == nil {
      state.restore(from: backup)
      return try parseCompoundLiteral(in: &state)
    }

    let output = try state.expect("type expression", using: parseExpr(in:))

    // Synthesize the environment as an empty tuple if we parsed `[]`.
    let s = state.lexer.sourceCode.emptyRange(at: opener.site.startIndex)
    let e = environment ?? AnyExprID(state.insert(TupleTypeExpr(elements: [], site: s)))

    let expr = state.insert(
      ArrowTypeExpr(
        receiverEffect: effect,
        environment: e,
        parameters: parameters,
        output: output,
        site: state.range(from: opener.site.startIndex)))
    return AnyExprID(expr)
  }

  private static func parseTupleOrParenthesizedExpr(
    in state: inout ParserState
  ) throws -> AnyExprID? {
    // Parse the elements.
    guard let elementList = try tupleExprElementList.parse(&state) else { return nil }

    // If there's only one element without any label and we didn't parse a trailing separator,
    // interpret the element's value as a parenthesized expression.
    if elementList.trailingSeparator == nil,
      let uniqueElement = elementList.elements.uniqueElement,
      uniqueElement.label == nil
    {
      return uniqueElement.value
    }

    let expr = state.insert(
      TupleExpr(
        elements: elementList.elements,
        site: state.range(from: elementList.opener.site.startIndex)))
    return AnyExprID(expr)
  }

  private static func parseTupleExprElement(
    in state: inout ParserState
  ) throws -> TupleExpr.Element? {
    let backup = state.backup()

    // Parse a labeled element.
    if let label = state.take(if: { $0.isLabel }) {
      if state.take(.colon) != nil {
        if let value = try expr.parse(&state) {
          return TupleExpr.Element(label: state.token(label), value: value)
        }
      }
    }

    // Backtrack and parse an unlabeled element.
    state.restore(from: backup)
    if let value = try expr.parse(&state) {
      return TupleExpr.Element(value: value)
    }

    return nil
  }

  private static func parseTupleTypeExpr(
    in state: inout ParserState
  ) throws -> TupleTypeExpr.ID? {
    // Parse the elements.
    guard let elementList = try tupleTypeExprElementList.parse(&state) else { return nil }

    return state.insert(
      TupleTypeExpr(
        elements: elementList.elements,
        site: state.range(from: elementList.opener.site.startIndex)))
  }

  private static func parseTupleTypeExprElement(
    in state: inout ParserState
  ) throws -> TupleTypeExpr.Element? {
    let backup = state.backup()

    // Parse a labeled element.
    if let label = state.take(if: { $0.isLabel }) {
      if state.take(.colon) != nil {
        if let type = try expr.parse(&state) {
          return TupleTypeExpr.Element(label: state.token(label), type: type)
        }
      }
    }

    // Backtrack and parse an unlabeled element.
    state.restore(from: backup)
    if let type = try expr.parse(&state) {
      return TupleTypeExpr.Element(type: type)
    }

    return nil
  }

  private static func parseCompoundLiteral(in state: inout ParserState) throws -> AnyExprID? {
    if let map = try parseMapLiteral(in: &state) {
      return AnyExprID(state.insert(map))
    }

    if let buffer = try bufferLiteral.parse(&state) {
      let expr = state.insert(
        BufferLiteralExpr(
          elements: buffer.elements,
          site: state.range(from: buffer.opener.site.startIndex)))
      return AnyExprID(expr)
    }

    return nil

  }

  private static let callArgument = Apply(parseArgument(in:))

  static let conditionalClause =
    (conditionalClauseItem.and(zeroOrMany(take(.comma).and(conditionalClauseItem).second))
      .map({ (_, tree) -> [ConditionItem] in [tree.0] + tree.1 }))

  static let conditionalClauseItem = Apply(parseConditionalClauseItem(in:))

  /// Parses a part of a conditional clause.
  private static func parseConditionalClauseItem(
    in state: inout ParserState
  ) throws -> ConditionItem? {
    if let item = try parseConditionalClauseBinding(in: &state) {
      return item
    } else {
      return try parseExpr(in: &state).map({ .expr($0) })
    }
  }

  /// Parses a binding declaration used as part of a conditional clause.
  private static func parseConditionalClauseBinding(
    in state: inout ParserState
  ) throws -> ConditionItem? {
    guard let pattern = try parseBindingPattern(in: &state) else { return nil }

    _ = try state.expect("'='", using: { $0.take(.assign) })
    let rhs = try state.expect("expression", using: parseExpr(in:))

    let s = state.ast[pattern].site
    let d = state.insert(
      BindingDecl(
        accessModifier: SourceRepresentable(value: .private, range: s),
        memberModifier: nil,
        pattern: pattern,
        initializer: rhs,
        site: s.extended(upTo: state.currentIndex)))
    return .decl(d)
  }

  // MARK: Comma-separated lists

  private static let staticArgumentList = DelimitedCommaSeparatedList(
    openerKind: .lAngle,
    closerKind: .rAngle,
    closerDescription: ">",
    elementParser: Apply(parseArgument(in:)))

  private static func parseStaticArgumentList(
    in state: inout ParserState
  ) throws -> [LabeledArgument]? {
    try parseList(in: &state, with: staticArgumentList)
  }

  private static let functionCallArgumentList = DelimitedCommaSeparatedList(
    openerKind: .lParen,
    closerKind: .rParen,
    closerDescription: ")",
    elementParser: Apply(parseArgument(in:)))

  private static func parseFunctionCallArgumentList(
    in state: inout ParserState
  ) throws -> [LabeledArgument]? {
    try parseList(in: &state, with: functionCallArgumentList)
  }

  private static let subscriptCallArgumentList = DelimitedCommaSeparatedList(
    openerKind: .lBrack,
    closerKind: .rBrack,
    closerDescription: "]",
    elementParser: Apply(parseArgument(in:)))

  private static func parseSubscriptCallArgumentList(
    in state: inout ParserState
  ) throws -> [LabeledArgument]? {
    try parseList(in: &state, with: subscriptCallArgumentList)
  }

  private static let attributeArgumentList = DelimitedCommaSeparatedList(
    openerKind: .lParen,
    closerKind: .rParen,
    closerDescription: ")",
    elementParser: Apply(parseAttributeArgument(in:)))

  private static func parseAttributeArgumentList(
    in state: inout ParserState
  ) throws -> [Attribute.Argument]? {
    try parseList(in: &state, with: attributeArgumentList)
  }

  private static let parameterList = DelimitedCommaSeparatedList(
    openerKind: .lParen,
    closerKind: .rParen,
    closerDescription: ")",
    elementParser: Apply(parseParameterDecl(in:)))

  private static func parseParameterList(
    in state: inout ParserState
  ) throws -> [ParameterDecl.ID]? {
    try parseList(in: &state, with: parameterList)
  }

  private static let arrowParameterList = DelimitedCommaSeparatedList(
    openerKind: .lParen,
    closerKind: .rParen,
    closerDescription: ")",
    elementParser: Apply(parseArrowParameter(in:)))

  private static func parseArrowParameterList(
    in state: inout ParserState
  ) throws -> [ArrowTypeExpr.Parameter]? {
    try parseList(in: &state, with: arrowParameterList)
  }

  private static func parseList<C: Combinator>(
    in state: inout ParserState,
    with parser: DelimitedCommaSeparatedList<C>
  ) throws -> [C.Element]? where C.Context == ParserState {
    guard let result = try parser.parse(&state) else { return nil }

    if let s = result.trailingSeparator, result.closer != nil {
      state.diagnostics.insert(.error(unexpectedToken: s))
    }

    return result.elements
  }

  private static let tupleExprElementList = DelimitedCommaSeparatedList(
    openerKind: .lParen,
    closerKind: .rParen,
    closerDescription: ")",
    elementParser: Apply(parseTupleExprElement(in:)))

  private static let tupleTypeExprElementList = DelimitedCommaSeparatedList(
    openerKind: .lBrace,
    closerKind: .rBrace,
    closerDescription: "}",
    elementParser: Apply(parseTupleTypeExprElement(in:)))

  private static let bufferLiteral = DelimitedCommaSeparatedList(
    openerKind: .lBrack,
    closerKind: .rBrack,
    closerDescription: "]",
    elementParser: Apply(parseExpr(in:)))

  private static let nonemptyMapLiteral = DelimitedCommaSeparatedList(
    openerKind: .lBrack,
    closerKind: .rBrack,
    closerDescription: "]",
    elementParser: Apply(parseMapElement(in:)))

  private static func parseMapElement(in state: inout ParserState) throws -> MapLiteralExpr.Element?
  {
    let backup = state.backup()

    if let lhs = try parseExpr(in: &state) {
      if state.take(.colon) != nil {
        if let rhs = try parseExpr(in: &state) {
          return MapLiteralExpr.Element(key: AnyExprID(lhs), value: AnyExprID(rhs))
        }
      }
    }

    state.restore(from: backup)
    return nil
  }

  private static func parseMapLiteral(in state: inout ParserState) throws -> MapLiteralExpr? {
    if let mapLiteral = state.take(.lBrack, .colon, .rBrack) {
      return MapLiteralExpr(elements: [], site: mapLiteral.first!.site)
    }

    let backup = state.backup()

    if let expr = try nonemptyMapLiteral.parse(&state), expr.closer != nil {
      return MapLiteralExpr(elements: expr.elements, site: expr.opener.site)
    }

    state.restore(from: backup)

    return nil
  }

  // MARK: Patterns

  private static func anyPattern<Base: Combinator>(
    _ base: Base
  ) -> AnyCombinator<ParserState, AnyPatternID>
  where Base.Context == ParserState, Base.Element: PatternID {
    AnyCombinator(parse: { (state) in
      try base.parse(&state).map(AnyPatternID.init(_:))
    })
  }

  private static func parsePattern(in state: inout ParserState) throws -> AnyPatternID? {
    // `_` is always a wildcard pattern.
    if let u = state.take(.under) {
      return AnyPatternID(state.insert(WildcardPattern(site: u.site)))
    }

    // Attempt to parse a binding pattern.
    if let p = try parseBindingPattern(in: &state) {
      // Complain if we're already parsing a binding pattern.
      if state.contexts.last == .bindingPattern {
        state.diagnostics.insert(.error(nestedBindingPattern: p, in: state.ast))
      }
      return AnyPatternID(p)
    }

    // Attempt to parse a tuple pattern.
    if let p = try tuplePattern.parse(&state) {
      return AnyPatternID(p)
    }

    // Attempt to parse a name or option pattern if we're in the context of a binding pattern.
    if state.contexts.last == .bindingPattern {
      if let p = try namePattern.parse(&state) {
        if let mark = state.takePostfixQuestionMark() {
          let s = state.ast[p].site.extended(toCover: mark.site)
          let o = state.insert(OptionPattern(name: p, site: s))
          return AnyPatternID(o)
        } else {
          return AnyPatternID(p)
        }
      }
    }

    // Default to an expression.
    guard let e = try expr.parse(&state) else { return nil }
    let p = state.insert(ExprPattern(expr: e, site: state.ast[e].site))
    return AnyPatternID(p)
  }

  private static let bindingPattern = Apply(parseBindingPattern(in:))

  static func parseBindingPattern(
    in state: inout ParserState
  ) throws -> BindingPattern.ID? {
    guard let introducer = try parseBindingIntroducer(in: &state) else { return nil }

    // Push the context.
    state.contexts.append(.bindingPattern)
    defer { state.contexts.removeLast() }

    // Parse the subpattern and its optional ascription.
    let subpattern = try state.expect("pattern", using: parsePattern(in:))
    let annotation = try parseAscription(in: &state, parseExpr(in:))

    return state.insert(
      BindingPattern(
        introducer: introducer,
        subpattern: subpattern,
        annotation: annotation,
        site: state.range(from: introducer.site.startIndex)))
  }

  /// Parses a binding introducer.
  ///
  /// Should not be called before checking if the next token is `_` if another wildcard rule could apply.
  private static func parseBindingIntroducer(
    in state: inout ParserState
  ) throws -> SourceRepresentable<BindingPattern.Introducer>? {
    guard let head = state.peek() else { return nil }

    // Interpret `_ = rhs` as a sugar for `let _ = rhs`
    if head.kind == .under {
      return SourceRepresentable(
        value: .let,
        range: state.lexer.sourceCode.emptyRange(at: state.currentIndex))
    }

    let introducer: BindingPattern.Introducer
    switch head.kind {
    case .let:
      _ = state.take()
      introducer = .let

    case .var:
      _ = state.take()
      introducer = .var

    case .inout:
      _ = state.take()
      introducer = .inout

    case .sink:
      _ = state.take()
      _ = try state.expect("'let'", using: { $0.take(.let) })
      introducer = .sinklet

    default:
      return nil
    }

    return SourceRepresentable(
      value: introducer,
      range: head.site.extended(upTo: state.currentIndex))
  }

  static let exprPattern =
    (Apply<ParserState, AnyPatternID>({ (state) -> AnyPatternID? in
      // Attempt to parse tuples as patterns as deeply as possible.
      if let patternID = try tuplePattern.parse(&state) {
        return AnyPatternID(patternID)
      }

      // Attempt to parse a name pattern if we're in the context of a binding pattern.
      if state.contexts.last == .bindingPattern {
        if let patternID = try namePattern.parse(&state) {
          return AnyPatternID(patternID)
        }
      }

      // Default to an expression.
      guard let exprID = try expr.parse(&state) else { return nil }
      let id = state.insert(
        ExprPattern(
          expr: exprID,
          site: state.ast[exprID].site))
      return AnyPatternID(id)
    }))

  static let namePattern =
    (take(.name).map(
      { (state, token) -> NamePattern.ID in
        let declID = state.insert(VarDecl(identifier: state.token(token)))
        return state.insert(NamePattern(decl: declID, site: token.site))
      }))

  static let tuplePattern =
    (take(.lParen).and(maybe(tuplePatternElementList)).and(take(.rParen))
      .map({ (state, tree) -> TuplePattern.ID in
        state.insert(
          TuplePattern(
            elements: tree.0.1 ?? [],
            site: tree.0.0.site.extended(upTo: tree.1.site.endIndex)))
      }))

  static let tuplePatternElementList =
    (tuplePatternElement.and(zeroOrMany(take(.comma).and(tuplePatternElement).second))
      .map({ (_, tree) -> [TuplePattern.Element] in [tree.0] + tree.1 }))

  static let tuplePatternElement =
    (Apply<ParserState, TuplePattern.Element>({ (state) in
      let backup = state.backup()

      // Parse a labeled element.
      if let label = state.take(if: { $0.isLabel }) {
        if state.take(.colon) != nil {
          if let value = try parsePattern(in: &state) {
            return TuplePattern.Element(label: state.token(label), pattern: value)
          }
        }
      }

      // Backtrack and parse an unlabeled element.
      state.restore(from: backup)
      if let value = try parsePattern(in: &state) {
        return TuplePattern.Element(label: nil, pattern: value)
      }

      return nil
    }))

  static let wildcardPattern =
    (take(.under)
      .map({ (state, token) -> WildcardPattern.ID in
        state.insert(WildcardPattern(site: token.site))
      }))

  // MARK: Statements

  private static func anyStmt<Base: Combinator>(
    _ base: Base
  ) -> AnyCombinator<ParserState, AnyStmtID>
  where Base.Context == ParserState, Base.Element: StmtID {
    AnyCombinator(parse: { (state) in
      try base.parse(&state).map(AnyStmtID.init(_:))
    })
  }

  static let stmt: Recursive<ParserState, AnyStmtID> = (Recursive(_stmt.parse(_:)))

  static let _stmt =
    (oneOf([
      anyStmt(braceStmt),
      anyStmt(discardStmt),
      anyStmt(Apply(parseConditionalStmt(in:))),
      anyStmt(doWhileStmt),
      anyStmt(whileStmt),
      anyStmt(forStmt),
      anyStmt(returnStmt),
      anyStmt(yieldStmt),
      anyStmt(breakStmt),
      anyStmt(continueStmt),
      anyStmt(bindingStmt),
      anyStmt(declStmt),
      anyStmt(exprStmt),
      anyStmt(compilerConditionStmt),
    ]))

  static let braceStmt =
    (take(.lBrace)
      .and(zeroOrMany(take(.semi)))
      .and(zeroOrMany(stmt.and(zeroOrMany(take(.semi))).first))
      .and(take(.rBrace))
      .map({ (state, tree) -> BraceStmt.ID in
        state.insert(
          BraceStmt(stmts: tree.0.1, site: tree.0.0.0.site.extended(upTo: state.currentIndex)))
      }))

  static let discardStmt =
    (take(.under).and(take(.assign)).and(expr)
      .map({ (state, tree) -> DiscardStmt.ID in
        state.insert(
          DiscardStmt(expr: tree.1, site: tree.0.0.site.extended(upTo: state.currentIndex)))
      }))

  private static func parseElseClause(
    in state: inout ParserState
  ) throws -> Introduced<AnyStmtID>? {
    guard let introducer = state.take(.else) else { return nil }

    if let s = try parseConditionalStmt(in: &state) {
      let s = AnyStmtID(s)
      return Introduced(s, at: introducer.site)
    } else {
      let s = AnyStmtID(try state.expect("'{'", using: braceStmt))
      return Introduced(s, at: introducer.site)
    }
  }

  /// Parses a conditional statement.
  private static func parseConditionalStmt(
    in state: inout ParserState
  ) throws -> ConditionalStmt.ID? {
    guard let introducer = state.take(.if) else { return nil }

    let c = try state.expect("condition", using: conditionalClause)
    let a = try state.expect("'{'", using: braceStmt)
    let b = try parseElseClause(in: &state)

    return state.insert(
      ConditionalStmt(
        introducerSite: introducer.site,
        condition: c, success: a, failure: b,
        site: state.range(from: introducer.site.startIndex)))
  }

  static let doWhileStmt =
    (take(.do).and(loopBody).and(take(.while)).and(expr)
      .map({ (state, tree) -> DoWhileStmt.ID in
        state.insert(
          DoWhileStmt(
            introducerSite: tree.0.0.0.site,
            body: tree.0.0.1, condition: Introduced(tree.1, at: tree.0.1.site),
            site: tree.0.0.0.site.extended(upTo: state.currentIndex)))
      }))

  static let whileStmt =
    (take(.while).and(conditionalClause).and(loopBody)
      .map({ (state, tree) -> WhileStmt.ID in
        state.insert(
          WhileStmt(
            introducerSite: tree.0.0.site,
            condition: tree.0.1, body: tree.1,
            site: tree.0.0.site.extended(upTo: state.currentIndex)))
      }))

  static let forStmt = Apply(parseForLoop(in:))

  /// Parses a for-loop.
  private static func parseForLoop(in state: inout ParserState) throws -> ForStmt.ID? {
    guard let introducer = state.take(.for) else { return nil }

    let binding = try state.expect("binding", using: parseForLoopBinding(in:))
    let domainIntroducer = try state.expect("in", using: { $0.take(.in) })
    let domain = try state.expect("expression", using: parseExpr(in:))
    let filter = try parseForLoopFilter(in: &state)
    let body = try state.expect("loop body", using: loopBody)

    return state.insert(
      ForStmt(
        introducerSite: introducer.site,
        binding: binding,
        domain: .init(domain, at: domainIntroducer.site),
        filter: filter, body: body,
        site: introducer.site.extended(upTo: state.currentIndex)))
  }

  /// Parses the binding of a for-loop.
  private static func parseForLoopBinding(in state: inout ParserState) throws -> BindingDecl.ID? {
    guard let pattern = try parseBindingPattern(in: &state) else { return nil }
    let s = state.ast[pattern].site
    return state.insert(
      BindingDecl(
        accessModifier: SourceRepresentable(value: .private, range: s),
        memberModifier: nil,
        pattern: pattern,
        initializer: nil,
        site: s))
  }

  /// Parses the filter of a for-loop.
  private static func parseForLoopFilter(
    in state: inout ParserState
  ) throws -> Introduced<AnyExprID>? {
    guard let introducer = state.take(.where) else { return nil }
    let e = try state.expect("expression", using: parseExpr(in:))
    return .init(e, at: introducer.site)
  }

  static let loopBody = inContext(.loopBody, apply: braceStmt)

  static let returnStmt =
    (take(.return).and(maybe(onSameLine(expr)))
      .map({ (state, tree) -> ReturnStmt.ID in
        state.insert(
          ReturnStmt(
            introducerSite: tree.0.site,
            value: tree.1,
            site: tree.0.site.extended(upTo: state.currentIndex)))
      }))

  static let yieldStmt =
    (take(.yield).and(onSameLine(expr))
      .map({ (state, tree) -> YieldStmt.ID in
        state.insert(
          YieldStmt(
            introducerSite: tree.0.site,
            value: tree.1,
            site: tree.0.site.extended(upTo: state.currentIndex)))
      }))

  static let breakStmt =
    (take(.break)
      .map({ (state, token) -> BreakStmt.ID in
        state.insert(BreakStmt(site: token.site))
      }))

  static let continueStmt =
    (take(.continue)
      .map({ (state, token) -> ContinueStmt.ID in
        state.insert(ContinueStmt(site: token.site))
      }))

  static let bindingStmt = Apply(parseBindingStmt(in:))

  /// Parses a binding statement.
  private static func parseBindingStmt(in state: inout ParserState) throws -> AnyStmtID? {
    guard let d = try parseBindingDecl(in: &state) else { return nil }

    if state.take(.else) == nil {
      // No fallback introducer; be satisfied with just the binding declaration.
      let s = state.insert(DeclStmt(decl: AnyDeclID(d), site: state.ast[d].site))
      return AnyStmtID(s)
    }

    if state.ast[d].initializer == nil {
      try fail(.error("conditional binding requires an initializer", at: state.ast[d].site))
    }

    let fallback = try state.expect("fallback", using: braceStmt.parse)
    let s = state.insert(
      ConditionalBindingStmt(
        binding: d,
        fallback: fallback,
        site: state.ast[d].site.extended(upTo: state.currentIndex)))
    return AnyStmtID(s)
  }

  static let declStmt =
    (Apply(parseDecl)
      .map({ (state, decl) -> DeclStmt.ID in
        state.insert(DeclStmt(decl: decl, site: state.ast[decl].site))
      }))

  static let exprStmt = Apply(parseExprOrAssignStmt(in:))

  private static func parseExprOrAssignStmt(in state: inout ParserState) throws -> AnyStmtID? {
    guard let lhs = try expr.parse(&state) else { return nil }

    // Return an expression statement unless the next token is `=`.
    guard let assign = state.take(.assign) else {
      let stmt = state.insert(
        ExprStmt(expr: lhs, site: state.ast[lhs].site))
      return AnyStmtID(stmt)
    }

    if !state.hasLeadingAndTrailingWhitespaces(assign) {
      state.diagnostics.insert(.error(assignOperatorRequiresWhitespaces: assign))
    }

    let rhs = try state.expect("expression", using: parseExpr(in:))

    let stmt = state.insert(
      AssignStmt(
        left: lhs,
        right: rhs,
        site: state.range(from: state.ast[lhs].site.startIndex)))
    return AnyStmtID(stmt)
  }

  static let compilerConditionStmt = Apply(parseCompilerConditionStmt(in:))

  private static func parseCompilerConditionStmt(
    in state: inout ParserState
  ) throws -> AnyStmtID? {
    try state.take(.poundIf).map { (head) in
      try parseCompilerConditionTail(head: head, in: &state)
    }
  }

  /// Parses a logical connective from `state`.
  private static func parseConnective(in state: inout ParserState) -> Connective? {
    // Next token must be an operator.
    guard let t = state.peek(), t.kind == .oper else { return nil }

    // The value of the token must be either `||` or `&&`.
    var r: Connective
    switch t.site.text {
    case "||":
      r = .disjunction
    case "&&":
      r = .conjunction
    default:
      return nil
    }

    // Consume the token and "succeed".
    _ = state.take()
    return r
  }

  /// Parses a `Condition` for a `ConditionalCompilationStmt`.
  private static func parseCondition(
    in state: inout ParserState
  ) throws -> ConditionalCompilationStmt.Condition {
    return try condition(withInfixConnectiveStrongerOrEqualTo: .disjunction, in: &state)

    /// Parses a condition as a proposition, a negation, or an infix sentence whose operator has
    /// a precedence at least as strong as `p`.
    func condition(
      withInfixConnectiveStrongerOrEqualTo p: Connective,
      in state: inout ParserState
    ) throws -> ConditionalCompilationStmt.Condition {
      var lhs = try parseCompilerCondition(in: &state)

      while true {
        // Tentatively parse a connective.
        let backup = state.backup()
        guard let c = parseConnective(in: &state) else { return lhs }

        // Backtrack if the connective we got hasn't strong enough precedence.
        if c.rawValue < p.rawValue {
          state.restore(from: backup)
          return lhs
        }

        // If we parsed `||` the RHS must be a conjunction. Otherwise it must be a proposition or
        // negation. In either case we'll come back here to parse the remainder of the expression.
        switch c {
        case .disjunction:
          let rhs = try condition(withInfixConnectiveStrongerOrEqualTo: .conjunction, in: &state)
          lhs = .or(lhs, rhs)
        case .conjunction:
          let rhs = try parseCompilerCondition(in: &state)
          lhs = .and(lhs, rhs)
        }
      }

      return lhs
    }
  }

  /// Parses a compiler condition structure, after the initial token (#if or #elseif).
  private static func parseCompilerConditionTail(
    head: Token, in state: inout ParserState
  ) throws -> AnyStmtID {
    // Parse the condition.
    let condition = try parseCondition(in: &state)

    // Parse the body of the compiler condition.
    let stmts: [AnyStmtID]
    if condition.mayNotNeedParsing && !condition.holds(for: state.ast.compilationConditions) {
      try skipConditionalCompilationBranch(in: &state, stoppingAtElse: true)
      stmts = []
    } else {
      stmts = try parseConditionalCompilationBranch(in: &state)
    }

    // Parse the other branch(es) of the condition.
    let fallback: [AnyStmtID]

    switch state.peek()?.kind {
    case .poundEndif:
      fallback = []
      _ = try state.expect("'#endif'", using: { $0.take(.poundEndif) })

    case .poundElse, .poundElseif:
      let h = state.take()!
      if condition.mayNotNeedParsing && condition.holds(for: state.ast.compilationConditions) {
        try skipConditionalCompilationBranch(in: &state, stoppingAtElse: false)
        fallback = []
        _ = try state.expect("'#endif'", using: { $0.take(.poundEndif) })
      } else if h.kind == .poundElse {
        fallback = try parseConditionalCompilationBranch(in: &state)
        _ = try state.expect("'#endif'", using: { $0.take(.poundEndif) })
      } else {
        fallback = [try parseCompilerConditionTail(head: h, in: &state)]
      }

    default:
      try fail(.error(expected: "statement, #endif, #else or #elseif", at: state.currentLocation))
    }

    let r = state.insert(
      ConditionalCompilationStmt(
        condition: condition,
        stmts: stmts,
        fallback: fallback,
        site: head.site.extended(upTo: state.currentIndex)))
    return AnyStmtID(r)
  }

  /// Skips the branch body of a conditional compilation statement and nested conditional compilation statements.
  private static func skipConditionalCompilationBranch(
    in state: inout ParserState, stoppingAtElse: Bool
  ) throws {
    var innerCompilerConditions = 0
    while let head = state.peek() {
      let closing: Bool
      switch head.kind {
      case .poundEndif:
        closing = true
      case .poundElse, .poundElseif:
        // Check if we need to stop at the corresponding #else[if].
        closing = stoppingAtElse && innerCompilerConditions == 0
      default: closing = false
      }
      if closing {
        if innerCompilerConditions == 0 {
          // We are done skipping all the tokens from the body.
          break
        } else {
          innerCompilerConditions -= 1
        }
      }
      // Consume this token.
      _ = state.take()

      // Are opening another nested compiler condition?
      if head.kind == .poundIf {
        innerCompilerConditions += 1
      }
    }
  }

  /// Parses the body of a compiler condition structure branch.
  private static func parseConditionalCompilationBranch(
    in state: inout ParserState
  ) throws -> [AnyStmtID] {
    let stmtsParser =
      (zeroOrMany(take(.semi))
        .and(zeroOrMany(stmt.and(zeroOrMany(take(.semi))).first))
        .second)
    return try stmtsParser.parse(&state) ?? []
  }

  /// Parses the condition of a compiler conditional.
  private static func parseCompilerCondition(
    in state: inout ParserState
  ) throws -> ConditionalCompilationStmt.Condition {
    if let boolLiteral = state.take(.bool) {
      return state.lexer.sourceCode[boolLiteral.site] == "true" ? .`true` : .`false`
    }

    if let op = state.take(.oper) {
      if state.token(op).value == "!" {
        return .not(try parseCompilerCondition(in: &state))
      } else {
        try fail(.error(expected: "compiler condition", at: state.currentLocation))
      }
    }

    if let name = state.take(.name) {
      let expectVersionNumber: Bool
      let conditionName = state.token(name).value
      switch conditionName {
      case "compiler_version", "hylo_version":
        expectVersionNumber = true
      default:
        expectVersionNumber = false
      }

      if expectVersionNumber {
        // Returns Int.
        let integerParser = (take(.int)).map { (state, tree) -> Int in
          Int(state.token(tree).value)!
        }
        // Returns SemanticVersion.
        let versionNumberParser =
          (integerParser.and(
            maybe(take(.dot).and(integerParser).and(maybe(take(.dot).and(integerParser))))
          ).map({
            (state, tree) -> SemanticVersion in
            SemanticVersion(major: tree.0, minor: tree.1?.0.1 ?? 0, patch: tree.1?.1?.1 ?? 0)
          }))
        let parser =
          (take(.lParen)  // => TakeKind
            .and(operatorIdentifier).second  // => SourceRepresentable<Identifier>
            .and(versionNumberParser)  // => (SourceRepresentable<Identifier>, SemanticVersion)
            .and(take(.rParen)).first  // => (SourceRepresentable<Identifier>, SemanticVersion)
          )
        guard let p = try parser.parse(&state) else {
          try fail(.error(expected: "version number comparison", at: state.currentLocation))
        }
        let comparison: ConditionalCompilationStmt.VersionComparison
        switch p.0.value {
        case ">=":
          comparison = .greaterOrEqual(p.1)
        case "<":
          comparison = .less(p.1)
        default:
          try fail(.error(expected: "'>=' or '<'", at: p.0.site.start))
        }
        switch conditionName {
        case "compiler_version":
          return .compilerVersion(comparison: comparison)
        case "hylo_version":
          return .hyloVersion(comparison: comparison)
        default:
          unreachable()
        }
      } else {
        // We have the form #if identifier(identifier), and our current parsing state starts at '('.
        let parser =
          (take(.lParen)  // => TakeKind
            .and(take(.name).map({ (state, token) -> String in state.token(token).value })).second
            // => String
            .and(take(.rParen)).first  // => String
          )
        guard let id = try parser.parse(&state) else {
          try fail(.error(expected: "identifier", at: state.currentLocation))
        }
        switch conditionName {
        case "os": return .operatingSystem(id)
        case "arch": return .architecture(id)
        case "feature": return .feature(id)
        case "compiler": return .compiler(id)
        default:
          try fail(.error(expected: "compiler condition", at: state.currentLocation))
        }
      }
    } else {
      try fail(.error(expected: "compiler condition", at: state.currentLocation))
    }
  }

  // MARK: Type expressions

  private static let nameTypeExpr = Apply(parseNameTypeExpr(in:))

  private static func parseNameTypeExpr(in state: inout ParserState) throws -> NameExpr.ID? {
    guard let expr = try parseCompoundExpr(in: &state) else { return nil }
    if let converted = NameExpr.ID(expr) {
      return converted
    } else {
      try fail(.error(expected: "name", at: state.ast[expr].site.start))
    }
  }

  private static func parseArrowParameter(
    in state: inout ParserState
  ) throws -> ArrowTypeExpr.Parameter? {
    let backup = state.backup()

    // Parse a labeled parameter.
    if let label = state.take(if: { $0.isLabel }) {
      if state.take(.colon) != nil {
        if let type = try parseParameterTypeExpr(in: &state) {
          return ArrowTypeExpr.Parameter(label: state.token(label), type: type)
        }
      }
    }

    // Backtrack and parse an unlabeled parameter.
    state.restore(from: backup)
    if let type = try parseParameterTypeExpr(in: &state) {
      return ArrowTypeExpr.Parameter(type: type)
    }

    return nil
  }

  /// Parses the type annotation of a parameter declaration.
  static func parseParameterTypeExpr(
    in state: inout ParserState
  ) throws -> NodeID<ParameterTypeExpr>? {
    let backup = state.backup()
    let startIndex = state.currentIndex

    let accessEffect = try passingConvention.parse(&state)

    var isAutoClosure = false
    if let introducer = state.take(if: { $0.kind == .attribute }) {
      let attribute = SourceRepresentable(
        value: Attribute(name: state.token(introducer), arguments: []),
        range: state.range(from: introducer.site.startIndex))
      if attribute.value.name.value == "@autoclosure" {
        isAutoClosure = true
      } else {
        state.diagnostics.insert(.error(unexpectedAttribute: attribute))
      }
    }

    guard let bareType = try expr.parse(&state) else {
      state.restore(from: backup)
      return nil
    }

    return state.insert(
      ParameterTypeExpr(
        convention: accessEffect
          ?? SourceRepresentable(
            value: .let,
            range: state.lexer.sourceCode.emptyRange(at: startIndex)),
        isAutoclosure: isAutoClosure,
        bareType: bareType,
        site: state.range(from: startIndex)
      ))
  }

  static let receiverEffect = accessEffect

  static let passingConvention = accessEffect

  static let accessEffect = translate([
    .let: AccessEffect.let,
    .inout: AccessEffect.inout,
    .set: AccessEffect.set,
    .sink: AccessEffect.sink,
    .yielded: AccessEffect.yielded,
  ])

  static let whereClause =
    (take(.where).and(whereClauseConstraintList)
      .map({ (state, tree) -> SourceRepresentable<WhereClause> in
        SourceRepresentable(
          value: WhereClause(introducerSite: tree.0.site, constraints: tree.1),
          range: tree.0.site.extended(upTo: state.currentIndex))
      }))

  static let whereClauseConstraintList =
    (whereClauseConstraint.and(zeroOrMany(take(.comma).and(whereClauseConstraint).second))
      .map({ (state, tree) -> [SourceRepresentable<WhereClause.ConstraintExpr>] in
        [tree.0] + tree.1
      }))

  static let whereClauseConstraint = (typeConstraint.or(valueConstraint))

  static let typeConstraint =
    (Apply<ParserState, SourceRepresentable<WhereClause.ConstraintExpr>>({ (state) in
      guard let lhs = try parseNameTypeExpr(in: &state) else { return nil }

      // equality-constraint
      if state.take(.equal) != nil {
        let rhs = try state.expect("type expression", using: parseExpr(in:))
        return SourceRepresentable(
          value: .equality(l: lhs, r: rhs),
          range: state.ast[lhs].site.extended(upTo: state.currentIndex))
      }

      // bound-constraint
      if state.take(.colon) != nil {
        let rhs = try state.expect("type expression", using: boundComposition)
        return SourceRepresentable(
          value: .bound(l: lhs, r: rhs),
          range: state.ast[lhs].site.extended(upTo: state.currentIndex))
      }

      try fail(.error(expected: "constraint operator", at: state.currentLocation))
    }))

  static let valueConstraint =
    (valueAttribute.and(expr)
      .map({ (state, tree) -> SourceRepresentable<WhereClause.ConstraintExpr> in
        SourceRepresentable(
          value: .value(tree.1),
          range: tree.0.site.extended(upTo: state.currentIndex))
      }))

  static let boundComposition =
    (nameTypeExpr.and(zeroOrMany(take(.ampersand).and(nameTypeExpr).second))
      .map({ (state, tree) -> [NameExpr.ID] in [tree.0] + tree.1 }))

  // MARK: Attributes

  /// Parses a list of attributes.
  static func parseAttributeList(
    in state: inout ParserState
  ) throws -> [SourceRepresentable<Attribute>]? {
    var result: [SourceRepresentable<Attribute>] = []
    while let e = try parseAttribute(in: &state) {
      result.append(e)
    }
    return result
  }

  /// Parses a single attribute.
  static func parseAttribute(
    in state: inout ParserState
  ) throws -> SourceRepresentable<Attribute>? {
    guard let introducer = state.take(.attribute) else { return nil }
    let arguments = try parseAttributeArgumentList(in: &state) ?? []

    return SourceRepresentable(
      value: Attribute(name: state.token(introducer), arguments: arguments),
      range: state.range(from: introducer.site.startIndex))
  }

  private static func parseAttributeArgument(
    in state: inout ParserState
  ) throws -> Attribute.Argument? {
    if let value = try parseExpr(in: &state) {
      return Attribute.Argument(value: value)
    }

    return nil
  }

  static let valueAttribute = attribute("@value")

}

/// The attributes and modifiers preceding a declaration.
struct DeclPrologue {

  /// Indicates whether the prologue is empty.
  let isEmpty: Bool

  /// The index of the first character in the prologue.
  let startIndex: String.Index

  /// The attributes in the prologue.
  let attributes: [SourceRepresentable<Attribute>]

  /// The access modifiers in the prologue.
  let accessModifiers: Set<SourceRepresentable<AccessModifier>>

  /// The member modifiers in the prologue.
  let memberModifiers: Set<SourceRepresentable<MemberModifier>>

  /// Indicates whether the prologue contains the `static` member modifier.
  var isStatic: Bool {
    memberModifiers.contains(where: { (m) in m.value == .static })
  }

}

/// The parsed head of a function declaration.
struct FunctionDeclHead {

  /// The site of the `fun` introducer.
  let introducerSite: SourceRange

  /// The stem of the declared identifier.
  let stem: SourceRepresentable<String>

  /// The notation of the declared function, if any.
  let notation: SourceRepresentable<OperatorNotation>?

  /// The generic clause of the declaration, if any.
  let genericClause: SourceRepresentable<GenericClause>?

  /// The capture list of the declaration.
  let captures: [BindingDecl.ID]

}

/// The parsed signature of a function declaration.
struct FunctionDeclSignature {

  /// The parameters of the declaration.
  let parameters: [ParameterDecl.ID]

  /// The receiver effect of the declaration, if any.
  let receiverEffect: SourceRepresentable<AccessEffect>?

  /// The return type annotation of the declaration, if any.
  let output: AnyExprID?

}

/// The body of a function or method declaration.
enum FunctionOrMethodDeclBody {

  case function(FunctionBody)

  case method([MethodImpl.ID])

}

/// The parsed head of a subscript declaration.
struct SubscriptDeclHead {

  /// The introducer of the declaration.
  let introducer: SourceRepresentable<SubscriptDecl.Introducer>

  /// The stem of the declared identifier, if any.
  let stem: SourceRepresentable<String>?

  /// The generic clause of the declaration, if any.
  let genericClause: SourceRepresentable<GenericClause>?

  /// The capture list of the declaration.
  let captures: [BindingDecl.ID]

}

/// The parsed head of a property declaration.
struct PropertyDeclHead {

  /// The introducer of the declaration.
  let introducer: SourceRepresentable<SubscriptDecl.Introducer>

  /// The stem of the declared identifier.
  let stem: SourceRepresentable<String>

}

/// The parsed signature of a subscript declaration.
struct SubscriptDeclSignature {

  /// The parameters of the declaration.
  let parameters: [ParameterDecl.ID]

  /// The return type annotation of the declaration.
  let output: AnyExprID

}

/// The parsed component of a name expression.
struct NameExprComponent {

  /// The site from which `self` was parsed.
  let site: SourceRange

  /// The name of the component.
  let name: SourceRepresentable<Name>

  /// The static arguments of the component.
  let arguments: [LabeledArgument]

}

/// The name and argument label of a parameter declaration.
struct ParameterInterface {

  /// The argument label of the parameter, if any.
  let label: SourceRepresentable<Identifier>?

  /// The name of the parameter.
  let name: SourceRepresentable<Identifier>

  /// The implicit marker of the parameter, if any.
  let implicitMarker: Token?

}

/// A conjunction (`&&`) or disjunction (`||`) operator.
enum Connective: Int {

  /// The logical disjunction.
  case disjunction

  /// The logical conjunction.
  case conjunction

}

/// A combinator that parses tokens with a specific kind.
struct TakeKind: Combinator {

  typealias Context = ParserState

  typealias Element = Token

  /// The kind of the token to consume.
  let kind: Token.Kind

  func parse(_ state: inout ParserState) throws -> Token? {
    state.take(kind)
  }

}

/// A combinator that parses contextual keywords.
struct ContextualKeyword<T: RawRepresentable>: Combinator where T.RawValue == String {

  typealias Context = ParserState

  typealias Element = SourceRepresentable<T>

  func parse(_ state: inout ParserState) throws -> Element? {
    if let next = state.peek(), next.kind == .name {
      if let value = T(rawValue: String(state.lexer.sourceCode[next.site])) {
        _ = state.take()
        return SourceRepresentable(value: value, range: next.site)
      }
    }
    return nil
  }

}

/// A combinator that updates the parsing contexts.
struct WrapInContext<Base: Combinator>: Combinator where Base.Context == ParserState {

  typealias Context = ParserState

  typealias Element = Base.Element

  /// The context in which `base` should be applied.
  let context: ParserState.Context

  /// The underlying combinator.
  public let base: Base

  func parse(_ state: inout ParserState) throws -> Element? {
    state.contexts.append(context)
    defer { state.contexts.removeLast() }
    return try base.parse(&state)
  }

}

/// A combinator that parses comma-separated lists of elements delimited by tokens on both ends.
struct DelimitedCommaSeparatedList<E: Combinator>: Combinator where E.Context == ParserState {

  typealias Context = ParserState

  /// The result of a comma-separated list parser.
  struct Element {

    /// The left delimiter of the list.
    let opener: Token

    /// The right delimiter of the list, if parsed.
    let closer: Token?

    /// The trailing comma, if parsed.
    let trailingSeparator: Token?

    /// The elements of the list.
    let elements: [E.Element]

  }

  /// The kind of the left delimiter.
  let openerKind: Token.Kind

  /// The kind of the right delimiter.
  let closerKind: Token.Kind

  /// The description of the right delimiter (for diagnostics).
  let closerDescription: String

  /// The parser recognizing the list's elements.
  let elementParser: E

  func parse(_ state: inout ParserState) throws -> Element? {
    // Parse the opening angle.
    guard let opener = state.take(openerKind) else { return nil }

    // Parse the elements.
    var elementWasParsed = false
    var elements: [E.Element] = []
    var trailingSeparator: Token? = nil
    var closer: Token? = nil

    while true {
      // Parse one element.
      let h = state.peek()
      if let element = try elementParser.parse(&state) {
        if !elements.isEmpty && trailingSeparator == nil {
          state.diagnostics.insert(.error(expected: "',' separator", at: h!.site.start))
        }

        elements.append(element)
        elementWasParsed = true
        trailingSeparator = nil

        if let t = state.take(.comma) {
          trailingSeparator = t
          continue
        }
      } else {
        elementWasParsed = false
      }

      // If we get here, we either parsed an element not followed by a separator (1), or we didn't
      // consume any token (2). In both case, we should expect the closing delimiter next.
      if let t = state.take(closerKind) {
        closer = t
        break
      }

      // If we got here by (2) but didn't parse any element, diagnose a missing delimiter and exit.
      if !elementWasParsed {
        state.diagnostics.insert(.error(expected: closerDescription, matching: opener, in: state))
        break
      }

      // If we got here by (1) and reached EOF, diagnose a missing delimiter and exit. Otherwise,
      // try to parse another element.
      if state.peek() == nil {
        state.diagnostics.insert(.error(expected: closerDescription, matching: opener, in: state))
        break
      }
    }

    return Element(
      opener: opener,
      closer: closer,
      trailingSeparator: trailingSeparator,
      elements: elements)
  }

}

/// Creates a combinator that parses tokens with the specified kind.
private func take(_ kind: Token.Kind) -> TakeKind {
  TakeKind(kind: kind)
}

/// Creates a combinator that parses name tokens with the specified value.
private func take(nameTokenWithValue value: String) -> Apply<ParserState, Token> {
  Apply({ (state) in state.take(nameTokenWithValue: value) })
}

/// Creates a combinator that parses attribute tokens with the specified name.
private func attribute(_ name: String) -> Apply<ParserState, Token> {
  Apply({ (state) in state.take(attribute: name) })
}

/// Creates a combinator that translates token kinds to instances of type.
private func translate<T>(
  _ table: [Token.Kind: T]
) -> Apply<ParserState, SourceRepresentable<T>> {
  Apply({ (state) in
    guard let head = state.peek() else { return nil }
    if let translation = table[head.kind] {
      _ = state.take()
      return SourceRepresentable(value: translation, range: head.site)
    } else {
      return nil
    }
  })
}

/// Creates a combinator that pushes `context` to the parser state before applying, and pops
/// that context afterward.
private func inContext<Base: Combinator>(
  _ context: ParserState.Context,
  apply base: Base
) -> WrapInContext<Base> {
  WrapInContext(context: context, base: base)
}

/// Creates a combinator that applies `base` only if its input is not preceded by whitespaces.
private func withoutLeadingWhitespace<Base: Combinator>(
  _ base: Base
) -> Apply<ParserState, Base.Element>
where Base.Context == ParserState {
  Apply({ (state) in try state.hasLeadingWhitespace ? nil : base.parse(&state) })
}

/// Creates a combinator that applies `base` only if its input is not preceded by newlines.
private func onSameLine<Base: Combinator>(
  _ base: Base
) -> Apply<ParserState, Base.Element>
where Base.Context == ParserState {
  Apply({ (state) in
    if let t = state.peek() {
      return try state.hasNewline(before: t)
        ? nil
        : base.parse(&state)
    } else {
      // Let `base` handle end of stream.
      return try base.parse(&state)
    }
  })
}

extension OperatorNotation {

  /// Creates an instance from `token`'s kind, or returns `nil` if `token` does not represent an
  /// operator notation.
  fileprivate init?(_ token: Token) {
    switch token.kind {
    case .infix: self = .infix
    case .prefix: self = .prefix
    case .postfix: self = .postfix
    default: return nil
    }
  }

}

extension ParserState {

  fileprivate func token(_ t: Token) -> SourceRepresentable<Identifier> {
    .init(value: String(lexer.sourceCode[t.site]), range: t.site)
  }

}
