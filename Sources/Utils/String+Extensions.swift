extension String.StringInterpolation {

  /// Appends the string descriptions of the elements in `list` separated by `separator`.
  public mutating func appendInterpolation<L: Sequence>(
    list: L,
    joinedBy separator: String = ", "
  ) {
    appendLiteral(list.descriptions(joinedBy: separator))
  }

}

extension StringProtocol {

  /// Removes trailing newlines from the given string subsequence.
  public func removingTrailingNewlines() -> Self.SubSequence {
    if let i = self.lastIndex(where: { !$0.isNewline }) {
      return self.prefix(through: i)
    } else {
      return self.prefix(upTo: startIndex)
    }
  }

  /// If `self` ends with `suffix`, `self` sans that `suffix`, or `self` otherwise.
  public func removingSuffix<S: Collection<Character>>(_ suffix: S) -> Self.SubSequence {
    if let i = index(endIndex, offsetBy: -suffix.count, limitedBy: startIndex),
      self[i...].elementsEqual(suffix)
    {
      return self[..<i]
    } else {
      return self[...]
    }
  }

  /// Returns the indices of the start of each line, in order.
  public func lineBoundaries() -> [Index] {
    var r = [startIndex]
    var remainder = self[...]
    while !remainder.isEmpty, let i = remainder.firstIndex(where: \.isNewline) {
      let j = index(after: i)
      r.append(j)
      remainder = remainder[j...]
    }
    return r
  }

  /// Returns each line of text in order, sans terminating newline.
  public func lineContents() -> [SubSequence] {
    var result: [SubSequence] = []
    var remainder = self[...]
    while !remainder.isEmpty {
      let i = remainder.firstIndex(where: \.isNewline) ?? remainder.endIndex
      result.append(remainder[..<i])
      remainder = remainder[i...].dropFirst()
    }
    return result
  }

  /// Replace any succession of whitespace characters (including newlines and tabs) with a single
  /// white space character.
  public func canonicalize() -> String {
    var remaining = self[..<self.endIndex]
    var result: String = ""
    while !remaining.isEmpty {
      // Skip all the whitespaces
      remaining = remaining.drop(while: { $0.isWhitespace })
      if !result.isEmpty {
        // The skipped whitespaces will be encoded as a single whitespace
        result.append(" ")
      }

      // Now, `remaining` starts with a non-whitespace
      // Find the next whitespace, i.e., continuous non-whitespace text
      let idx = remaining.firstIndex(where: { $0.isWhitespace }) ?? self.endIndex

      // Copy non-whitespace text, and advance the text we need to copy
      result.append(contentsOf: remaining[..<idx])
      remaining = remaining[idx..<self.endIndex]
    }

    return result
  }

  /// Returns `self` in snake_case, given it is in PascalCase or camelCase.
  public func snakeCased() -> String {
    var result: String = ""
    var i = startIndex
    while i != endIndex {
      if !self[i].isUppercase {
        result.append(self[i])
        i = index(after: i)
        continue
      }

      let s = self[i...].prefix(while: \.isUppercase)
      if s.count > 1 {
        result.append(contentsOf: s.dropLast().lowercased())
        result.append("_")
        result.append(s.last!.lowercased())
        i = s.endIndex
        continue
      }

      if (i != startIndex) && (self[index(before: i)] != "_") {
        result.append("_")
      }
      result.append(self[i].lowercased())
      i = index(after: i)
    }
    return result
  }

}

extension String {

  /// `self` in which escaped sequences have been replaced by the characters that they represent.
  public var unescaped: String {
    let entities = ["\0", "\t", "\n", "\r", "\"", "\'", "\\"]
    var current = self
    for e in entities {
      let s = String(e.debugDescription.dropFirst().dropLast())
      current = current.replacingOccurrences(of: s, with: e)
    }
    return current
  }

}
