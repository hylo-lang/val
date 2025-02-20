import DequeModule
import Durian

/// A type representing the state of the parser.
struct ParserState {

  /// A tag representing the context of the parser.
  enum Context {

    case bindingPattern

    case captureList

    case extensionBody

    case functionBody

    case loopBody

    case namespaceBody

    case productBody

    case subscriptBody

    case topLevel

    case traitBody

  }

  /// The AST being constructed by the parser.
  var ast: AST

  /// The node space into which new node identities must be registered.
  private let space: Int

  /// The lexer generating the tokens to parse.
  private(set) var lexer: Lexer

  /// The current index of the parser in the character stream.
  private(set) var currentIndex: String.Index

  /// The lookahead buffer.
  private var lookahead = Deque<Token>()

  /// The diagnostics of the parse errors and warnings.
  var diagnostics: DiagnosticSet

  /// A stack describing the parsing context.
  var contexts: [Context] = []

  /// Creates a new context for parsing parts of `ast`, registering the identities of newly
  /// formed ASTs in space `k`, using `lexer` to generate tokens and reporting errors to `log`.
  init(ast: AST, space: Int, lexer: Lexer, reportingDiagnosticsTo log: DiagnosticSet? = nil) {
    self.ast = ast
    self.space = space
    self.lexer = lexer
    self.currentIndex = lexer.sourceCode.text.startIndex
    self.diagnostics = log ?? DiagnosticSet()
  }

  /// Indicates whether the parser is at global scope.
  var isAtGlobalScope: Bool { isAtModuleScope || isAtNamespaceScope }

  /// Indicates whether the parser is at module scope.
  var isAtModuleScope: Bool { contexts.isEmpty }

  /// Indicates whether the parser is at namespace scope.
  var isAtNamespaceScope: Bool { contexts.last == .namespaceBody }

  /// Indicates whether the parser is expecting to parse member declarations.
  var isAtTypeScope: Bool {
    if let c = contexts.last {
      return (c == .extensionBody) || (c == .productBody) || (c == .traitBody)
    } else {
      return false
    }
  }

  /// Indicates whether the parser is at trait scope.
  var isAtTraitScope: Bool { contexts.last == .traitBody }

  /// Indicates whether the parser is expecting to parse a capture declaration.
  var isParsingCaptureList: Bool { contexts.last == .captureList }

  /// The current location of the parser in the character stream.
  var currentLocation: SourcePosition {
    lexer.sourceCode.position(currentIndex)
  }

  /// The next character in the character stream, unless the parser reached its end.
  var currentCharacter: Character? { isAtEOF ? nil : lexer.sourceCode.text[currentIndex] }

  /// Returns whether the parser is at the end of the character stream.
  var isAtEOF: Bool { currentIndex == lexer.sourceCode.text.endIndex }

  /// Returns whether there is a whitespace at the current index.
  var hasLeadingWhitespace: Bool {
    currentIndex < lexer.sourceCode.text.endIndex
      && lexer.sourceCode.text[currentIndex].isWhitespace
  }

  /// Returns whether there are whitespaces before *and* after `token`.
  mutating func hasLeadingAndTrailingWhitespaces(_ token: Token) -> Bool {
    guard
      let a = lexer.sourceCode.text.prefix(upTo: token.site.startIndex).last,
      let b = lexer.sourceCode.text.suffix(from: token.site.endIndex).first
    else { return false }
    return a.isWhitespace && b.isWhitespace
  }

  /// Returns whether there is a new line in the character stream before `bound`.
  mutating func hasNewline(before bound: Token) -> Bool {
    lexer.sourceCode.text[currentIndex..<bound.site.startIndex]
      .contains(where: { $0.isNewline })
  }

  /// Returns a site from `startIndex` to `self.currentIndex`.
  func range(from startIndex: String.Index) -> SourceRange {
    lexer.sourceCode.range(startIndex..<currentIndex)
  }

  /// Returns whether `token` is a member index.
  func isMemberIndex(_ token: Token) -> Bool {
    (token.kind == .int)
      && lexer.sourceCode[token.site].allSatisfy({ ch in
        guard let ascii = ch.asciiValue else { return false }
        return (0x30...0x39) ~= ascii
      })
  }

  /// Returns the next token without consuming it, if any.
  mutating func peek() -> Token? {
    // Return the token in the lookahead buffer, if available.
    if let token = lookahead.first {
      return token
    }

    // Attempt to pull a new element from the lexer.
    guard let token = lexer.next() else { return nil }
    lookahead.append(token)
    return token
  }

  /// Returns up to the next `n` next tokens without consuming them.
  mutating func peek(_ n: Int) -> Deque<Token>.SubSequence {
    while lookahead.count < n {
      guard let t = lexer.next() else { break }
      lookahead.append(t)
    }
    return lookahead.prefix(upTo: min(n, lookahead.count))
  }

  /// Returns whether a token of the given `kind` is next in the input.
  mutating func isNext(_ kind: Token.Kind) -> Bool {
    peek()?.kind == kind
  }

  /// Returns whether a token satisfying `predicate` is next in the input.
  mutating func isNext(satisfying predicate: (Token) -> Bool) -> Bool {
    if let token = peek() {
      return predicate(token)
    } else {
      return false
    }
  }

  /// Consumes and returns the next token, if any.
  mutating func take() -> Token? {
    // Return the token in the lookahead buffer, if available.
    if let token = lookahead.popFirst() ?? lexer.next() {
      currentIndex = token.site.endIndex
      return token
    } else {
      return nil
    }
  }

  /// Consumes and returns the next token if it has the specified kind.
  mutating func take(_ kind: Token.Kind) -> Token? {
    if peek()?.kind == kind {
      let token = lookahead.removeFirst()
      currentIndex = token.site.endIndex
      return token
    } else {
      return nil
    }
  }

  /// Consumes and returns the first `kinds.count` tokens if they have the specified kinds.
  mutating func take(_ kinds: Token.Kind...) -> [Token]? {
    let tokens = peek(kinds.count)

    if tokens.elementsEqual(kinds, by: { (a, b) in a.kind == b }) {
      lookahead.removeFirst(kinds.count)
      currentIndex = tokens.last!.site.endIndex
      return Array(tokens)
    }

    return nil
  }

  /// Consumes and returns the next token, only if it has the specified kind and if it is not
  /// preceded by any whitespace.
  mutating func takeWithoutSkippingWhitespace(_ kind: Token.Kind) -> Token? {
    if hasLeadingWhitespace { return nil }
    return take(kind)
  }

  /// Consumes and returns the next token iff it is a single question mark nor preceded by any
  /// whitespace.
  mutating func takePostfixQuestionMark() -> Token? {
    if hasLeadingWhitespace { return nil }
    return take(if: { [source = lexer.sourceCode] in
      ($0.kind == .oper) && (source[$0.site] == "?")
    })
  }

  /// Consumes and returns the next token if it satisfies `predicate`.
  mutating func take(if predicate: (Token) -> Bool) -> Token? {
    if let token = peek(), predicate(token) {
      let token = lookahead.removeFirst()
      currentIndex = token.site.endIndex
      return token
    } else {
      return nil
    }
  }

  /// Consumes and returns a name token with the specified value.
  mutating func take(nameTokenWithValue value: String) -> Token? {
    take(if: { [source = lexer.sourceCode] in
      ($0.kind == .name) && (source[$0.site] == value)
    })
  }

  /// Consumes and returns an operator (excluding `=`) from the token stream.
  ///
  /// If the next token in the stream is an angle bracket, it is interpreted as an operator and
  /// merged with any attached operator.
  mutating func takeOperator() -> SourceRepresentable<Identifier>? {
    guard let head = peek() else { return nil }

    switch head.kind {
    case .oper, .ampersand, .equal, .pipe:
      _ = take()
      return SourceRepresentable(value: String(lexer.sourceCode[head.site]), range: head.site)

    case .lAngle, .rAngle:
      // Operator starts with `<` or `>`.
      _ = take()

      // Merge the leading angle bracket with attached operators.
      var upper = head.site.endIndex
      while let next = take(if: { $0.isOperatorPart && (upper == $0.site.startIndex) }) {
        upper = next.site.endIndex
      }

      let range = head.site.file.range(head.site.startIndex..<upper)
      return SourceRepresentable(value: String(lexer.sourceCode[range]), range: range)

    default:
      return nil
    }
  }

  /// Consumes and returns the value of a member index.
  mutating func takeMemberIndex() -> SourceRepresentable<Int>? {
    if let index = take(if: isMemberIndex(_:)) {
      return SourceRepresentable(value: Int(lexer.sourceCode[index.site])!, range: index.site)
    } else {
      return nil
    }
  }

  /// Consumes and returns an attribute token with the specified name.
  mutating func take(attribute name: String) -> Token? {
    take(if: { [source = lexer.sourceCode] in
      ($0.kind == .attribute) && (source[$0.site] == name)
    })
  }

  /// Applies `parse`, propagating thrown errors, and returns non-`nil` results or throws an error
  /// diagnosing that we expected `expectedConstruct`.
  mutating func expect<T>(
    _ expectedConstruct: String,
    using parse: (inout ParserState) throws -> T?
  ) throws -> T {
    if let element = try parse(&self) {
      return element
    } else {
      diagnostics.insert(.error(expected: expectedConstruct, at: currentLocation))
      throw diagnostics
    }
  }

  /// Applies `parser.parse`, propagating thrown errors, and returns non-`nil` results or throws
  /// an error diagnosing that we expected `expectedConstruct`.
  mutating func expect<C: Combinator>(
    _ expectedConstruct: String,
    using parser: C
  ) throws -> C.Element where C.Context == Self {
    try expect(expectedConstruct, using: parser.parse(_:))
  }

  /// Consumes tokens as long as they satisfy `predicate`.
  mutating func skip(while predicate: (Token) -> Bool) {
    while take(if: predicate) != nil {}
  }

  /// Consumes tokens until the first one that may be at the start of a declaration.
  mutating func skipUntilNextDecl() {
    skip(while: { (next) in !next.mayBeginDecl })
  }

  /// Inserts `n` into `self.ast`, accumulating any diagnostics in `self.diagnostics`.
  mutating func insert<T: Node>(_ n: T) -> T.ID {
    ast.insert(n, inNodeSpace: space, reportingDiagnosticsTo: &diagnostics)
  }

  /// Inserts `n` into `self.ast`.
  ///
  /// - Precondition: `n` is well-formed.
  mutating func insert<T: Node>(synthesized n: T) -> T.ID {
    ast.insert(synthesized: n, inNodeSpace: space)
  }
}

extension ParserState: Restorable {

  typealias Backup = Self

}
