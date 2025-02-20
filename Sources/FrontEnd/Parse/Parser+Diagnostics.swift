extension Diagnostic {

  static func error(assignOperatorRequiresWhitespaces token: Token) -> Diagnostic {
    .error("assignment operator requires whitespaces on both sides", at: token.site)
  }

  static func error(expected kind: Token.Kind, at location: SourcePosition) -> Diagnostic {
    error(expected: "'\(kind)'", at: location)
  }

  static func error(expected subject: String, at location: SourcePosition, notes: [Diagnostic] = [])
    -> Diagnostic
  {
    .error("expected \(subject)", at: location..<location, notes: notes)
  }

  static func error(
    expected closerDescription: String, matching opener: Token, in state: ParserState
  ) -> Diagnostic {
    .error(
      expected: "'\(closerDescription)'", at: state.currentLocation,
      notes: [
        .note("to match this '\(state.lexer.sourceCode[opener.site])'", at: opener.site)
      ])
  }

  static func error(infixOperatorRequiresWhitespacesAt site: SourceRange) -> Diagnostic {
    .error("infix operator requires whitespaces on both sides", at: site)
  }

  static func error(separatedMutationMarkerAt site: SourceRange) -> Diagnostic {
    .error("in-place mutation marker cannot be separated from its expression", at: site)
  }

  static func error(separatedPrefixOperatorAt site: SourceRange) -> Diagnostic {
    .error("prefix operator cannot be separated from its operand", at: site)
  }

  static func error(unexpectedToken token: Token) -> Diagnostic {
    .error("unexpected token '\(token.kind)'", at: token.site)
  }

  static func error(unterminatedCommentStartingAt p: SourcePosition) -> Diagnostic {
    .error("unterminated comment", at: p..<p)
  }

  static func error(unterminatedStringStartingAt p: SourcePosition) -> Diagnostic {
    .error("unterminated string", at: p..<p)
  }

  static func error(duplicateAccessModifier m: SourceRepresentable<AccessModifier>) -> Diagnostic {
    .error("duplicate access modifier '\(m.value)'", at: m.site)
  }

  static func error(
    inconsistentAccessModifiers m: SourceRepresentable<AccessModifier>,
    appearsAfterPreviousAccessModifier p: SourceRepresentable<AccessModifier>
  ) -> Diagnostic {
    .error(
      "inconsistent access modifier '\(m.value)'", at: m.site,
      notes: [
        .note("previously declared as '\(p.value)'", at: p.site)
      ])
  }

  static func error(
    duplicateImplementationIntroducer i: SourceRepresentable<AccessEffect>
  ) -> Diagnostic {
    .error("duplicate implementation introducer '\(i.value)'", at: i.site)
  }

  static func error(duplicateMemberModifier m: SourceRepresentable<MemberModifier>) -> Diagnostic {
    .error("duplicate member modifier '\(m.value)'", at: m.site)
  }

  static func error(
    memberModifier member: SourceRepresentable<MemberModifier>,
    appearsBeforeAccessModifier access: SourceRepresentable<AccessModifier>
  ) -> Diagnostic {
    .error(
      "member modifier '\(member.value)' must appear after access modifier '\(access.value)'",
      at: member.site)
  }

  static func error(unexpectedAccessModifier m: SourceRepresentable<AccessModifier>) -> Diagnostic {
    .error("unexpected access modifier '\(m.value)'", at: m.site)
  }

  static func error(unexpectedAttribute a: SourceRepresentable<Attribute>) -> Diagnostic {
    .error("unexpected attribute '\(a.value.name.value)'", at: a.value.name.site)
  }

  static func error(unexpectedInitializerDecl d: InitializerDecl) -> Diagnostic {
    .error("initializer declaration is not allowed here", at: d.introducer.site)
  }

  static func error(unexpectedEffect e: SourceRepresentable<AccessEffect>) -> Diagnostic {
    .error("unexpected effect '\(e.value)'", at: e.site)
  }

  static func error(nestedBindingPattern p: BindingPattern.ID, in ast: AST) -> Diagnostic {
    .error(
      "'\(ast[p].introducer.value)' cannot appear nested in another binding pattern",
      at: ast[p].introducer.site)
  }

  static func error(unknownPragma n: Substring, at site: SourceRange) -> Diagnostic {
    .error("unknown pragma '\(n)'", at: site)
  }

  static func error(
    illegalAccessModifierForImplicitParameter e: SourceRepresentable<AccessEffect>
  ) -> Diagnostic {
    .error("'\(e.value)'-parameter cannot be implicit", at: e.site)
  }

  static func error(declarationRequiresDefinitionAt site: SourceRange) -> Diagnostic {
    .error("declaration requires definition", at: site)
  }

}
