/// A part of an AST node that may have a textual representation in source code.
///
/// - Note: The source range is a non-salient annotation. It does not contribute to a node's value.
public struct SourceRepresentable<Part> {

  /// The part.
  public let value: Part

  /// The source range from which `part` was extracted.
  public let origin: SourceRange

  /// Creates a source representable container, annotating a value with an optional source range.
  public init(value: Part, range: SourceRange) {
    self.value = value
    self.origin = range
  }

}

extension SourceRepresentable: Equatable where Part: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    l.value == r.value
  }

}

extension SourceRepresentable: Hashable where Part: Hashable {

  public func hash(into hasher: inout Hasher) {
    value.hash(into: &hasher)
  }

}

extension SourceRepresentable: Codable where Part: Codable {

  fileprivate enum CodingKeys: String, CodingKey {

    case value, range

  }

  public init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)
    value = try container.decode(Part.self, forKey: .value)
    origin = try container.decode(SourceRange.self, forKey: .range)
  }

  public func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)
    try container.encode(value, forKey: .value)
    try container.encode(origin, forKey: .range)
  }

}
