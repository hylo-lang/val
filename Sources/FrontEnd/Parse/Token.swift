/// A terminal symbol of the syntactic grammar.
public struct Token {

  /// The kind of a token.
  public enum Kind: Int {

    // Errors
    case invalid = 0
    case unterminatedString
    case unterminatedBlockComment

    // Scalar literals
    case bool = 1000
    case exponent
    case int
    case string

    // Identifiers
    case name = 2000
    case under

    // Keywords
    case `any` = 3000
    case `break`
    case `catch`
    case `conformance`
    case `continue`
    case `do`
    case `else`
    case `extension`
    case `for`
    case `fun`
    case `if`
    case `import`
    case `in`
    case `infix`
    case `init`
    case `inout`
    case `internal`
    case `let`
    case `match`
    case `namespace`
    case `operator`
    case `postfix`
    case `prefix`
    case `property`
    case `private`
    case `public`
    case `remote`
    case `return`
    case `set`
    case `sink`
    case `some`
    case `spawn`
    case `static`
    case `subscript`
    case `trait`
    case `try`
    case `type`
    case `typealias`
    case `var`
    case `where`
    case `while`
    case `yield`
    case `yielded`

    case `poundElse`
    case `poundElseif`
    case `poundEndif`
    case `poundIf`

    // Attributes
    case attribute = 4000

    // Pragmas
    case pragmaLiteral = 5000

    // Operators
    case oper = 6000
    case ampersand
    case cast
    case arrow
    case assign
    case equal
    case pipe

    // Punctuation
    case comma = 7000
    case semi
    case dot
    case colon
    case twoColons

    // Delimiters
    case lParen = 8000
    case rParen
    case lBrace
    case rBrace
    case lBrack
    case rBrack
    case lAngle
    case rAngle

  }

  /// The kind of the token.
  public internal(set) var kind: Kind

  /// The site from which `self` was extracted.
  public internal(set) var site: SourceRange

  /// Indicates whether `self` is a keyword.
  public var isKeyword: Bool {
    (Kind.any.rawValue..<Kind.any.rawValue + 999) ~= kind.rawValue
  }

  /// Indicates whether `self` is a suitable as a label.
  public var isLabel: Bool {
    (kind == .name) || isKeyword
  }

  /// Indicates whether `self` may be in an operator.
  ///
  /// Operators may be represented by one or more tokens. For example, `<<` is
  /// represented by two consecutive `.lAngle` tokens. Use this property to determine whether
  /// `self` may be a token in such a sequence.
  public var isOperatorPart: Bool {
    isOf(kind: [.oper, .ampersand, .assign, .equal, .pipe, .lAngle, .rAngle])
  }

  /// Indicates whether `self` is a suitable prefix operator head.
  ///
  /// - Note: `&` may not be at the start of a prefix operator. An expression prefixed by `&` is
  ///   parsed as an in-place expression.
  public var isPrefixOperatorHead: Bool {
    isOf(kind: [.oper, .equal, .pipe, .rAngle])
  }

  /// Indicates whether `self` is a suitable postfix operator head.
  public var isPostfixOperatorHead: Bool {
    isOf(kind: [.oper, .ampersand, .equal, .pipe])
  }

  /// Indicates whether `self` is a declaration modifier.
  public var isDeclModifier: Bool {
    switch kind {
    case .public, .static, .private, .internal:
      return true
    default:
      return false
    }
  }

  /// Indicates whether `self` may be at the beginning of a declaration.
  public var mayBeginDecl: Bool {
    switch kind {
    case .`conformance`,
      .`extension`,
      .`fun`,
      .`import`,
      .`infix`,
      .`init`,
      .`inout`,
      .`let`,
      .`namespace`,
      .`operator`,
      .`postfix`,
      .`prefix`,
      .`property`,
      .`sink`,
      .`subscript`,
      .`trait`,
      .`type`,
      .`typealias`,
      .`var`:
      return true

    default:
      return isDeclModifier
    }
  }

  /// Indicates whether `self` may be at the beginning of a control statement.
  public var mayBeginCtrlStmt: Bool {
    switch kind {
    case .break, .continue, .for, .if, .lBrace, .return, .while:
      return true
    default:
      return false
    }
  }

  /// Returns whether `self.kind` is contained in `kinds`.
  ///
  /// - Parameter kinds: A list of kinds.
  public func isOf<T: Collection>(kind kinds: T) -> Bool where T.Element == Kind {
    kinds.contains(kind)
  }

}
