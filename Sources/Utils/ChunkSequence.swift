/// A collection contiguous slices partitioning a some base collection.
public struct Chunks<Base: Collection> {

  /// The collection being partitioned.
  private let base: Base

  /// The maximum number of elements in a single chunk.
  private let chunkCapacity: Int

  /// Creates an instance that partitions `base` into batches at most `maxCount` slices.
  ///
  /// If `maxCount` is greater than or equal to `base.count`, `self` will contain `base.count`
  /// collections of one element from `base`. Otherwise, `self` will contain `maxCount` elements
  /// of at most `base.count / maxCount + 1` element.
  ///
  /// - Requires: `maxCount > 0`
  public init(partitioning base: Base, inMax maxCount: Int) {
    precondition(maxCount > 0)
    self.base = base
    let q = base.count / maxCount
    self.chunkCapacity = (base.count % maxCount == 0) ? q : q + 1
  }

  /// Returns `base`.
  public func joined() -> Base {
    base
  }

}

extension Chunks: Collection {

  /// A position in `Chunks`.
  public typealias Index = Base.Index

  /// An element in `Chunks`.
  public typealias Element = Base.SubSequence

  /// The first position in `self`.
  public var startIndex: Index {
    base.startIndex
  }

  /// The "past the end" position in `self`.
  public var endIndex: Index {
    base.endIndex
  }

  /// The position after `i` in `self`.
  public func index(after i: Index) -> Index {
    base.index(i, offsetBy: chunkCapacity, limitedBy: base.endIndex) ?? endIndex
  }

  /// Accesses the chunk at `position`.
  public subscript(position: Index) -> Element {
    base[position..<index(after: position)]
  }

}

extension Collection {

  /// Returns a partition of self with at most `maxCount` chunks.
  public func chunked(inMax maxCount: Int) -> Chunks<Self> {
    .init(partitioning: self, inMax: maxCount)
  }

}
