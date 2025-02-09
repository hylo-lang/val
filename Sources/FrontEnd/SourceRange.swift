/// A half-open range of textual positions in a source file.
public struct SourceRange: Hashable {

  /// The file containing the source text.
  public let file: SourceFile

  /// The region of text in `file`'s contents.
  public let regionOfFile: Range<SourceFile.Index>

  /// The start of the region of text.
  public var startIndex: SourceFile.Index { regionOfFile.lowerBound }

  /// The end index of the range.
  public var endIndex: SourceFile.Index { regionOfFile.upperBound }

  /// Creates an instance with the given properties.
  public init(_ regionOfFile: Range<SourceFile.Index>, in file: SourceFile) {
    self.file = file
    self.regionOfFile = regionOfFile
  }

  /// Returns whether `self` contains the given location.
  public func contains(_ l: SourcePosition) -> Bool {
    (l.file == file) && regionOfFile.contains(l.index)
  }

  /// The start.
  public var start: SourcePosition {
    file.position(startIndex)
  }

  /// The end.
  public var end: SourcePosition {
    file.position(endIndex)
  }

  /// Returns a copy of `self` with the end increased (if necessary) to `newEnd`.
  public func extended(upTo newEnd: SourceFile.Index) -> SourceRange {
    precondition(newEnd >= endIndex)
    return file.range(startIndex ..< newEnd)
  }

  /// Returns a copy of `self` extended to cover `other`.
  public func extended(toCover other: SourceRange) -> SourceRange {
    precondition(file == other.file, "incompatible ranges")
    return file.range(
      Swift.min(startIndex, other.startIndex) ..< Swift.max(endIndex, other.endIndex))
  }

  /// Increases (if necessary) the end of `self` so that it equals `newEnd`.
  public mutating func extend(upTo newEnd: SourceFile.Index) {
    self = self.extended(upTo: newEnd)
  }

  /// Returns a copy of `self` extended to cover `other`.
  public mutating func extend(toCover other: SourceRange) {
    self = self.extended(toCover: other)
  }

  /// The source text contained in this range.
  public var text: Substring {
    file.text[regionOfFile]
  }

  /// Creates an empty range that starts and end at `p`.
  public static func empty(at p: SourcePosition) -> Self {
    SourceRange(p.index ..< p.index, in: p.file)
  }

}

extension SourceRange: Codable {

  fileprivate enum CodingKeys: String, CodingKey {

    case file, start, end

  }

  public init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)
    file = try container.decode(SourceFile.self, forKey: .file)
    let start = String.Index(
      utf16Offset: try container.decode(Int.self, forKey: .start),
      in: file.text)
    let end = String.Index(
      utf16Offset: try container.decode(Int.self, forKey: .end),
      in: file.text)
    regionOfFile = start ..< end
  }

  public func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)
    try container.encode(file, forKey: .file)
    try container.encode(startIndex.utf16Offset(in: file.text), forKey: .start)
    try container.encode(endIndex.utf16Offset(in: file.text), forKey: .end)
  }

}

extension SourceRange: CustomStringConvertible {

  /// A textual representation per the
  /// [Gnu-standard](https://www.gnu.org/prep/standards/html_node/Errors.html).
  public var gnuStandardText: String {
    let start = self.start.lineAndColumn
    let head = "\(file.url.relativePath):\(start.line).\(start.column)"
    if regionOfFile.isEmpty { return head }

    let end = file.position(endIndex).lineAndColumn
    if end.line == start.line {
      return head + "-\(end.column)"
    }
    return head + "-\(end.line).\(end.column)"
  }
  

  public var description: String { gnuStandardText }

}
