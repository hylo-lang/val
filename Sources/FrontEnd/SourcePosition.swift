/// A character boundary in a source file.
public struct SourcePosition: Hashable {

  /// The source file containing the position.
  public let file: SourceFile

  /// The position relative to the source file.
  public let index: String.Index

  /// Creates an instance with the given properties.
  public init(_ index: String.Index, in file: SourceFile) {
    self.file = file
    self.index = index
  }

  /// Creates an instance referring to the given 1-based line and column numbers in `source`.
  ///
  /// - Precondition: `line` and `column` denote a valid position in `source`.
  public init(line: Int, column: Int, in file: SourceFile) {
    self.file = file
    self.index = file.index(line: line, column: column)
  }

  /// The line which `self` resides.
  public var line: SourceLine { file.line(containing: index) }

  /// The line and column number of this position.
  public var lineAndColumn: (line: Int, column: Int) {
    let r = file.lineAndColumn(index)
    return (r.line, r.column)
  }

  /// Returns a site from `l` to `r`.
  ///
  /// - Requires: `l.file == r.file`
  public static func ..< (l: Self, r: Self) -> SourceRange {
    precondition(l.file == r.file, "incompatible locations")
    return l.file.range(l.index..<r.index)
  }

}

extension SourcePosition: Comparable {

  public static func < (l: Self, r: Self) -> Bool {
    precondition(l.file == r.file, "incompatible locations")
    return l.index < r.index
  }

}

extension SourcePosition: Codable {

  fileprivate enum CodingKeys: String, CodingKey {

    case file, index

  }

  public init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)
    file = try container.decode(SourceFile.self, forKey: .file)
    index = String.Index(
      utf16Offset: try container.decode(Int.self, forKey: .index),
      in: file.text)
  }

  public func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)
    try container.encode(file, forKey: .file)
    try container.encode(index.utf16Offset(in: file.text), forKey: .index)
  }

}

extension SourcePosition: CustomStringConvertible {

  public var description: String {
    let (line, column) = lineAndColumn
    return "\(file.url.relativePath):\(line):\(column)"
  }

}
