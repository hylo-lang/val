import Utils

/// A collection of declaration identifiers.
public struct DeclIDs {

  /// Instances are notionally the concatenation of two collections `front` and `back` such that
  /// `front` only contains type extending declarations and `back` contains none. `insert(_:)`
  /// maintains this invariant as well as the relative order of the elements in these collections.

  /// All identifiers in `self`.
  private(set) var all: [AnyDeclID]

  /// The position immediately after the last ID of a type extending declaration in `all`.
  private var extensionEndIndex: Int

  /// Creates an empty instance.
  public init() {
    all = []
    extensionEndIndex = 0
  }

  /// Creates an instance with the contents of each collection in `batch`.
  public init<S: Sequence<DeclIDs>>(formingUnionOf batch: S) {
    all = []

    var end: [AnyDeclID] = []
    for c in batch {
      all.append(contentsOf: c[..<c.extensionEndIndex])
      end.append(contentsOf: c[c.extensionEndIndex...])
    }

    extensionEndIndex = all.endIndex
    all.append(contentsOf: end)
  }

  /// The identifiers in `self` denoting type extending declarations.
  public var extensions: ArraySlice<AnyDeclID> {
    all[0..<extensionEndIndex]
  }

  /// The identifiers in `self` _not_ denoting type extending declarations.
  public var withoutExtensions: ArraySlice<AnyDeclID> {
    all[extensionEndIndex...]
  }

  /// Inserts `d` in `self`.
  public mutating func insert(_ d: AnyDeclID) {
    if d.isTypeExtendingDecl {
      all.insert(d, at: extensionEndIndex)
      extensionEndIndex += 1
    } else {
      all.append(d)
    }
  }

}

extension DeclIDs: Equatable {}

extension DeclIDs: RandomAccessCollection {

  public typealias Index = Int

  public typealias Element = AnyDeclID

  public var startIndex: Int { 0 }

  public var endIndex: Int { all.endIndex }

  public func index(after position: Int) -> Int {
    position + 1
  }

  public func index(before position: Int) -> Int {
    position - 1
  }

  public func index(_ position: Int, offsetBy distance: Int) -> Int {
    position + distance
  }

  public subscript(position: Int) -> AnyDeclID {
    all[position]
  }

}
