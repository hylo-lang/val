import Utils

/// A type that tokenize a source file.
public struct Lexer: IteratorProtocol, Sequence {

  /// The Hylo source being tokenized.
  public let sourceCode: SourceFile

  /// The current position in the source file.
  private(set) var index: String.Index

  private let profiler: ProfilingMeasurements?

  /// Creates a lexer generating tokens from the contents of `source`.
  public init(tokenizing source: SourceFile, profileWith profiler: ProfilingMeasurements? = nil) {
    self.sourceCode = source
    self.index = source.text.startIndex
    self.profiler = profiler
  }

  /// The current location of the lexer in `sourceCode`.
  public var location: SourcePosition { sourceCode.position(index) }

  /// `true` iff the last scanned token was `.int`.
  private var previousTokenWasInt = false

  /// Advances to the next token and returns it, or returns `nil` if no next token exists.
  public mutating func next() -> Token? {
    // Start measuring Lexer time
    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.Lexer)
    defer { probe?.stop() }

    // Skip whitespaces and comments.
    while true {
      if index == sourceCode.text.endIndex { return nil }

      // Skip whitespaces.
      if sourceCode.text[index].isWhitespace {
        previousTokenWasInt = false
        discard()
        continue
      }

      // Skip line comments.
      if take(prefix: "//") != nil {
        while (index < sourceCode.text.endIndex) && !sourceCode.text[index].isNewline {
          discard()
        }
        continue
      }

      // Skip block comments.
      if let start = take(prefix: "/*") {
        // Search for the end of the block.
        var open = 1
        while open > 0 {
          if take(prefix: "/*") != nil {
            open += 1
          } else if take(prefix: "*/") != nil {
            open -= 1
          } else if index < sourceCode.text.endIndex {
            discard()
          } else {
            return Token(
              kind: .unterminatedBlockComment,
              site: sourceCode.range(start..<index))
          }
        }

        // Found the end of the block.
        continue
      }

      // The next character must be part of a token.
      break
    }

    // Scan a new token.
    let head = sourceCode.text[index]
    var token = Token(kind: .invalid, site: location..<location)

    // Try scan for exponent if previous token was .int
    if previousTokenWasInt, let next = peek(), next == "e" || next == "E" {
      discard()
      if scanIntegralLiteral(allowingPlus: true) != nil {
        token.kind = .exponent
      }
      token.site.extend(upTo: index)
      return token
    }
    previousTokenWasInt = false

    // Scan names and keywords.
    if head.isLetter || (head == "_") {
      let word = take(while: { $0.isLetter || $0.isDecDigit })
      token.site.extend(upTo: index)

      switch word {
      case "_": token.kind = .under
      case "any": token.kind = .`any`
      case "break": token.kind = .`break`
      case "catch": token.kind = .`catch`
      case "conformance": token.kind = .`conformance`
      case "continue": token.kind = .`continue`
      case "do": token.kind = .`do`
      case "else": token.kind = .`else`
      case "extension": token.kind = .`extension`
      case "for": token.kind = .`for`
      case "fun": token.kind = .`fun`
      case "if": token.kind = .`if`
      case "import": token.kind = .`import`
      case "in": token.kind = .`in`
      case "infix": token.kind = .`infix`
      case "init": token.kind = .`init`
      case "inout": token.kind = .`inout`
      case "internal": token.kind = .`internal`
      case "let": token.kind = .`let`
      case "match": token.kind = .`match`
      case "namespace": token.kind = .`namespace`
      case "operator": token.kind = .`operator`
      case "postfix": token.kind = .`postfix`
      case "prefix": token.kind = .`prefix`
      case "property": token.kind = .`property`
      case "private": token.kind = .`private`
      case "public": token.kind = .`public`
      case "remote": token.kind = .`remote`
      case "return": token.kind = .`return`
      case "set": token.kind = .`set`
      case "sink": token.kind = .`sink`
      case "some": token.kind = .`some`
      case "spawn": token.kind = .`spawn`
      case "static": token.kind = .`static`
      case "subscript": token.kind = .`subscript`
      case "trait": token.kind = .`trait`
      case "try": token.kind = .`try`
      case "type": token.kind = .`type`
      case "typealias": token.kind = .`typealias`
      case "var": token.kind = .`var`
      case "where": token.kind = .`where`
      case "while": token.kind = .`while`
      case "yield": token.kind = .`yield`
      case "yielded": token.kind = .`yielded`

      case "false": token.kind = .bool
      case "true": token.kind = .bool

      case "is": token.kind = .cast

      case "as":
        _ = take("!") ?? take("*")
        token.site.extend(upTo: index)
        token.kind = .cast

      default:
        token.kind = .name
      }

      return token
    }

    // Scan a back-quoted names.
    if head == "`" {
      discard()

      if let c = peek(), c.isLetter {
        let i = index
        _ = take(while: { $0.isLetter || $0.isDecDigit })

        if peek() == "`" {
          let start = sourceCode.position(sourceCode.text.index(after: token.site.startIndex))
          token.kind = .name
          token.site = start..<location
          discard()
          return token
        } else {
          index = i
        }
      }

      token.site.extend(upTo: index)
      return token
    }

    // Scan integral literals.
    if let k = scanIntegralLiteral(allowingPlus: false) {
      token.kind = k
      token.site.extend(upTo: index)
      previousTokenWasInt = true
      return token
    }

    // Scan character strings.
    if head == "\"" {
      discard()

      var escape = false
      while index < sourceCode.text.endIndex {
        if !escape && (take("\"") != nil) {
          token.kind = .string
          token.site.extend(upTo: index)
          return token
        } else if take("\\") != nil {
          escape = !escape
        } else {
          discard()
          escape = false
        }
      }

      token.kind = .unterminatedString
      token.site.extend(upTo: index)
      return token
    }

    // Scan attributes.
    if head == "@" {
      discard()
      token.kind = take(while: { $0.isLetter || ($0 == "_") }).isEmpty ? .invalid : .attribute
      token.site.extend(upTo: index)
      return token
    }

    // Scan pragmas & pound-control keywords.
    if head == "#" {
      discard()
      let tail = take(while: { $0.isLetter || ($0 == "_") })
      token.site.extend(upTo: index)

      switch tail {
      case "if":
        token.kind = .poundIf
      case "else":
        token.kind = .poundElse
      case "elseif":
        token.kind = .poundElseif
      case "endif":
        token.kind = .poundEndif
      case "":
        token.kind = .invalid
      default:
        token.kind = .pragmaLiteral
      }

      return token
    }

    // Scan operators.
    if head.isOperator {
      let oper: Substring
      switch head {
      case "<", ">":
        // Leading angle brackets are tokenized individually, to parse generic clauses.
        discard()
        oper = sourceCode.text[token.site.startIndex..<index]

      default:
        oper = take(while: { $0.isOperator })
      }

      switch oper {
      case "<": token.kind = .lAngle
      case ">": token.kind = .rAngle
      case "->": token.kind = .arrow
      case "&": token.kind = .ampersand
      case "|": token.kind = .pipe
      case "=": token.kind = .assign
      case "==": token.kind = .equal
      default: token.kind = .oper
      }

      token.site.extend(upTo: index)
      return token
    }

    // Scan punctuation.
    switch head {
    case ",": token.kind = .comma
    case ";": token.kind = .semi
    case "(": token.kind = .lParen
    case ")": token.kind = .rParen
    case "{": token.kind = .lBrace
    case "}": token.kind = .rBrace
    case "[": token.kind = .lBrack
    case "]": token.kind = .rBrack

    case ".":
      // Scan range operators.
      if (take(prefix: "...") ?? take(prefix: "..<")) != nil {
        token.kind = .oper
        token.site.extend(upTo: index)
        return token
      }

      // Fall back to a simple dot.
      token.kind = .dot

    case ":":
      // Scan double colons.
      if take(prefix: "::") != nil {
        token.kind = .twoColons
        token.site.extend(upTo: index)
        return token
      }

      // Fall back to a simple colon.
      token.kind = .colon

    default:
      break
    }

    // Either the token is punctuation, or it's kind is `invalid`.
    discard()
    token.site.extend(upTo: index)
    return token
  }

  /// Discards `count` characters from the stream.
  private mutating func discard(_ count: Int = 1) {
    index = sourceCode.text.index(index, offsetBy: count)
  }

  /// Returns the next character in the stream without consuming it, if any.
  private func peek() -> Character? {
    if index == sourceCode.text.endIndex { return nil }
    return sourceCode.text[index]
  }

  /// Returns the current index and consumes `character` from the stream, or returns `nil` if the
  /// stream starts with a different character.
  public mutating func take(_ character: Character) -> String.Index? {
    if peek() != character { return nil }
    defer { index = sourceCode.text.index(after: index) }
    return index
  }

  /// Returns the current index and consumes `prefix` from the stream, or returns `nil` if the
  /// stream starts with a different prefix.
  private mutating func take<T: Sequence>(prefix: T) -> String.Index?
  where T.Element == Character {
    var newIndex = index
    for ch in prefix {
      if newIndex == sourceCode.text.endIndex || sourceCode.text[newIndex] != ch {
        return nil
      }
      newIndex = sourceCode.text.index(after: newIndex)
    }

    defer { index = newIndex }
    return index
  }

  /// Consumes the longest substring that satisfies the given predicate.
  private mutating func take(while predicate: (Character) -> Bool) -> Substring {
    let start = index
    while let ch = peek(), predicate(ch) {
      index = sourceCode.text.index(after: index)
    }

    return sourceCode.text[start..<index]
  }

  /// Consumes an integral literal and returns its kind, or returns `nil` if it fails to scan a valid integer.
  ///
  /// - Parameter allowingPlus: If set to `true`, allows the integral literal to begin with a "+" sign.
  ///                           If set to `false` (the default), only allows "-" or no sign at the beginning.
  private mutating func scanIntegralLiteral(allowingPlus allowPlus: Bool = false) -> Token.Kind? {
    let i = (allowPlus ? take("+") : nil) ?? take("-") ?? index
    guard let head = peek(), head.isDecDigit else {
      index = i
      return nil
    }

    // Check if the literal is non-decimal.
    if let i = take("0") {
      switch peek() {
      case "x":
        discard()
        if let c = peek(), c.isHexDigit {
          _ = take(while: { $0.isHexDigit })
          return .int
        }

      case "o":
        discard()
        if let c = peek(), c.isOctDigit {
          _ = take(while: { $0.isOctDigit })
          return .int
        }

      case "b":
        discard()
        if let c = peek(), c.isBinDigit {
          _ = take(while: { $0.isBinDigit })
          return .int
        }

      default:
        break
      }

      index = i
    }

    // Consume the integer part.
    _ = take(while: { $0.isDecDigit })
    return .int
  }

}

extension Character {

  /// Indicates whether `self` character represents a decimal digit.
  fileprivate var isDecDigit: Bool {
    guard let ascii = asciiValue else { return false }
    return (0x30...0x39) ~= ascii  // 0 ... 9
      || 0x5f == ascii  // _
  }

  /// Indicates whether `self` represents an hexadecimal digit.
  fileprivate var isHexDigit: Bool {
    guard let ascii = asciiValue else { return false }
    return (0x30...0x39) ~= ascii  // 0 ... 9
      || (0x41...0x46) ~= ascii  // A ... F
      || (0x61...0x66) ~= ascii  // a ... f
      || 0x5f == ascii  // _
  }

  /// /// Indicates whether `self` represents an octal digit.
  fileprivate var isOctDigit: Bool {
    guard let ascii = asciiValue else { return false }
    return (0x30...0x37) ~= ascii  // 0 ... 7
      || 0x5f == ascii  // _
  }

  /// Indicates whether `self` represents a binary digit.
  fileprivate var isBinDigit: Bool {
    self == "0" || self == "1" || self == "_"
  }

  /// Indicates whether `self` represents an operator.
  fileprivate var isOperator: Bool {
    "<>=+-*/%&|!?^~".contains(self)
  }

}
