import Algorithms

extension Collection {

  /// Accesses the unique element of the collection.
  ///
  /// This property is `nil` unless `self.count == 1`.
  public var uniqueElement: Element? {
    count == 1 ? self[startIndex] : nil
  }

  /// The first element of `self` and its suffix after its first index or `nil` if `self` is empty.
  public var headAndTail: (head: Element, tail: SubSequence)? {
    if isEmpty { return nil }
    return (head: self[startIndex], tail: self[index(after: startIndex)...])
  }

  /// Returns the minimal elements of `self` using `compare` to order them.
  ///
  /// A minimal element of a set *S* with a strict partial order *R* is an element not smaller than
  /// any other element in *S*. If *S* is a finite set and *R* is a strict total order, the notions
  /// of minimal element and minimum coincide.
  ///
  /// - Complexity: O(*n*^2) where *n* is the length of `self`.
  public func minimalElements(
    by compare: (Element, Element) -> StrictPartialOrdering
  ) -> [Element] {
    if let u = uniqueElement { return [u] }

    // This algorithm successively eliminates elements that are not minimal until all candidates
    // have been considered. All elements are candidates at the start. Then, each candidate is
    // compared with others. Greater elements are moved beyond the end of the candidate list while
    // incomparable ones are left in place. At each point, elements left of the current candidate
    // are known to be incomparable with each others and smaller than eliminated elements.

    var candidates = Array(indices)
    var end = candidates.count
    var i = 0
    var j = 1

    while i < end {
      while j < end {
        switch compare(self[candidates[i]], self[candidates[j]]) {
        case .ascending, .equal:
          candidates.swapAt(j, end - 1)
          end -= 1

        case .descending:
          candidates.swapAt(i, end - 1)
          end -= 1
          j = i + 1

        case nil:
          j += 1
        }
      }

      i += 1
      j = i + 1
    }

    return candidates[0..<end].map({ self[$0] })
  }

}

extension BidirectionalCollection where Element: Equatable {

  /// Returns `(head: a, tail: b)` where `a` is the prefix up to the last occurrence of `element`
  /// and `b` contains the remaining elements. `a` is empty if `element` is not in `self`.
  ///
  /// - Complexity: O(*n*), where *n* is the length of the collection.
  public func split(atLastIndexOf element: Element) -> (head: SubSequence, tail: SubSequence) {
    let i = lastIndex(of: element) ?? startIndex
    return (prefix(upTo: i), suffix(from: i))
  }

}

extension RangeReplaceableCollection {

  /// Filters this collection to keep only the elements satisfying `isIncluded`.
  public mutating func filterInPlace(_ isIncluded: (Element) throws -> Bool) rethrows {
    try removeAll(where: { (e) in try !isIncluded(e) })
  }

}

extension Collection where Self == Self.SubSequence {

  /// Removes `prefix` from the beginning and returns `true`, or returns `false` if `self`
  /// has no such prefix.
  public mutating func removeLeading<P: Collection>(_ prefix: P) -> Bool
  where P.Element == Element, Element: Equatable {
    var me = self[...]
    var p = prefix[...]

    while let x = me.first, let y = p.first {
      if x != y { return false }
      me = me.dropFirst()
      p = p.dropFirst()
    }

    if !p.isEmpty { return false }
    self = me
    return true
  }

  /// Removes elements from the beginning until the first element satisfies `shouldBeKept` or `self`
  /// is empty, returning the removed subsequence.
  @discardableResult
  public mutating func removeFirstUntil(it shouldBeKept: (Element) -> Bool) -> Self {
    return removeFirstWhile(it: { !shouldBeKept($0) })
  }

  /// Removes elements from the beginning that satisfy `shouldBeRemoved`, returning the removed
  /// subsequence.
  @discardableResult
  public mutating func removeFirstWhile(it shouldBeRemoved: (Element) -> Bool) -> Self {
    let t = self.drop(while: shouldBeRemoved)
    defer { self = t }
    return self[..<t.startIndex]
  }

}
