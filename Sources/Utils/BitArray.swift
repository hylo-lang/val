/// An array of bit values represented as Booleans, where `true` indicates that the bit is on.
public struct BitArray {

  /// A position in a `BitArray`.
  public struct Position: Comparable {

    /// The bucket containing `self`.
    fileprivate let bucket: Int

    /// The offset of `self` in its containing bucket.
    fileprivate let offsetInBucket: Int

    /// Creates a position from an index.
    fileprivate init(_ index: Int) {
      self.bucket = index >> UInt.bitWidth.trailingZeroBitCount
      self.offsetInBucket = index & (UInt.bitWidth - 1)
    }

    /// Creates a position with the given properties.
    ///
    /// - Requires: `offsetInBucket < UInt.bitCount`.
    fileprivate init(bucket: Int, offsetInBucket: Int) {
      self.bucket = bucket
      self.offsetInBucket = offsetInBucket
    }

    /// Returns the index corresponding to this position.
    fileprivate var index: Int {
      (bucket >> UInt.bitWidth.trailingZeroBitCount) + offsetInBucket
    }

    public static func < (l: Self, r: Self) -> Bool {
      if l.bucket == r.bucket {
        return l.offsetInBucket < r.offsetInBucket
      } else {
        return l.bucket < r.bucket
      }
    }

  }

  /// The value of each bit in the map, represented as a contiguous array of words.
  private var bits: [UInt]

  /// The number of bits in the array.
  public private(set) var count: Int

  /// Creates an empty array.
  public init() {
    bits = Array()
    count = 0
  }

  /// Creates a new array containing `count` elements with the value `b`.
  public init(repeating b: Bool, count: Int) {
    let k = 1 + ((count - 1) >> UInt.bitWidth.trailingZeroBitCount)
    self.bits = .init(repeating: b ? ~0 : 0, count: k)
    self.count = count
  }

  /// Creates an array copying the given `contents`.
  public init<S: Sequence<Bool>>(_ contents: S) {
    self = .init()
    reserveCapacity(contents.underestimatedCount)
    for b in contents { append(b) }
  }

  /// `true` iff `self` is empty.
  public var isEmpty: Bool {
    count == 0
  }

  /// `true` iff all elements in `self` are `false`.
  public var allFalse: Bool {
    if isEmpty { return true }

    let k = (count - 1) >> UInt.bitWidth.trailingZeroBitCount
    for i in 0..<k {
      if bits[i] != 0 { return false }
    }
    let m = (1 as UInt) << (count & (UInt.bitWidth - 1)) - 1
    return (bits[k] & m) == 0
  }

  /// `true` iff all elements in `self` are `true`.
  public var allTrue: Bool {
    if isEmpty { return true }

    let k = (count - 1) >> UInt.bitWidth.trailingZeroBitCount
    for i in 0..<k {
      if bits[i] != ~(0 as UInt) { return false }
    }
    let m = (1 as UInt) << (count & (UInt.bitWidth - 1)) - 1
    return (bits[k] & m) == m
  }

  /// The number of bits that the array can contain before allocating new storage.
  public var capacity: Int {
    bits.capacity << UInt.bitWidth.trailingZeroBitCount
  }

  /// Reserves enough space to store `n` bits in `self`.
  public mutating func reserveCapacity(_ n: Int) {
    if n == 0 { return }
    let k = 1 + ((n - 1) >> UInt.bitWidth.trailingZeroBitCount)
    bits.reserveCapacity(k)
  }

  /// Adds a new element at the end of the array.
  public mutating func append(_ bit: Bool) {
    let p = Position(count)
    if p.bucket >= bits.count {
      bits.append(bit ? 1 : 0)
    } else {
      setValue(bit, for: p)
    }
    count += 1
  }

  /// Removes and returns the last element in `self` if it isn't empty; otherwise returns `nil`.
  public mutating func popLast() -> Bool? {
    count == 0 ? nil : removeLast()
  }

  /// Removes and returns the last element in `self`.
  ///
  /// - Requires: `self` is not empty.
  @discardableResult
  public mutating func removeLast() -> Bool {
    precondition(count > 0, "array is empty")
    defer { count -= 1 }
    return self[count - 1]
  }

  /// Removes all elements from the array, keeping existing storage if `keepingCapacity` is `true`.
  public mutating func removeAll(keepingCapacity: Bool = false) {
    count = 0
    bits.removeAll(keepingCapacity: keepingCapacity)
  }

  /// Returns the bitwise OR of `lhs` and `rhs`.
  ///
  /// - Requires: `self.count == other.count`.
  public static func | (lhs: Self, rhs: Self) -> Self {
    var r = lhs
    r |= rhs
    return r
  }

  /// Writes the bitwise OR of `lhs` and `rhs` to `lhs`.
  ///
  /// - Requires: `self.count == other.count`.
  public static func |= (lhs: inout Self, rhs: Self) {
    lhs.applyBitwise(rhs, |)
  }

  /// Returns the bitwise AND of `lhs` and `rhs`.
  ///
  /// - Requires: `self.count == other.count`.
  public static func & (lhs: Self, rhs: Self) -> Self {
    var r = lhs
    r &= rhs
    return r
  }

  /// Writes the bitwise AND of `lhs` and `rhs` to `lhs`.
  ///
  /// - Requires: `self.count == other.count`.
  public static func &= (lhs: inout Self, rhs: Self) {
    lhs.applyBitwise(rhs, &)
  }

  /// Returns the bitwise XOR of `lhs` and `rhs`.
  ///
  /// - Requires: `self.count == other.count`.
  public static func ^ (lhs: Self, rhs: Self) -> Self {
    var r = lhs
    r ^= rhs
    return r
  }

  /// Writes the bitwise XOR of `lhs` and `rhs` to `lhs`.
  ///
  /// - Requires: `self.count == other.count`.
  public static func ^= (lhs: inout Self, rhs: Self) {
    lhs.applyBitwise(rhs, ^)
  }

  /// Assigns each bits in `self` to the result of `operation` applied on those bits and their
  /// corresponding bits in `other`.
  ///
  /// - Requires: `self.count == other.count`.
  private mutating func applyBitwise(_ other: Self, _ operation: (UInt, UInt) -> UInt) {
    precondition(self.count == other.count)
    if isEmpty { return }

    let k = (count - 1) >> UInt.bitWidth.trailingZeroBitCount
    for i in 0..<k {
      bits[i] = operation(bits[i], other.bits[i])
    }
    let m = (1 as UInt) << (count & (UInt.bitWidth - 1)) - 1
    bits[k] = operation(bits[k] & m, other.bits[k] & m)
  }

  /// Sets the value `b` for the bit at position `p`.
  ///
  /// - Requires: `p` is a valid position in `self`.
  private mutating func setValue(_ b: Bool, for p: Position) {
    let m = (1 as UInt) << p.offsetInBucket
    if b {
      bits[p.bucket] |= m
    } else {
      bits[p.bucket] &= ~m
    }
  }

}

extension BitArray: Equatable {

  public static func == (l: Self, r: Self) -> Bool {
    if l.count != r.count { return false }
    if l.isEmpty { return true }

    let k = (l.count - 1) >> UInt.bitWidth.trailingZeroBitCount
    if !l.bits.prefix(k).elementsEqual(r.bits.prefix(k)) {
      return false
    }

    let m = (1 as UInt) << (l.count & (UInt.bitWidth - 1)) - 1
    return (l.bits[k] & m) == (r.bits[k] & m)
  }

}

extension BitArray: Hashable {

  public func hash(into hasher: inout Hasher) {
    if isEmpty {
      hasher.combine(0)
      return
    }

    let k = (count - 1) >> UInt.bitWidth.trailingZeroBitCount
    bits.prefix(k).hash(into: &hasher)
    let m = (1 as UInt) << (count & (UInt.bitWidth - 1)) - 1
    (bits[k] & m).hash(into: &hasher)
  }

}

extension BitArray: MutableCollection {

  public typealias Index = Position

  public typealias Element = Bool

  public var startIndex: Position {
    .init(0)
  }

  public var endIndex: Position {
    .init(count)
  }

  public func index(after p: Position) -> Position {
    if p.offsetInBucket == 63 {
      return .init(bucket: p.bucket + 1, offsetInBucket: 0)
    } else {
      return .init(bucket: p.bucket, offsetInBucket: p.offsetInBucket + 1)
    }
  }

  public subscript(_ p: Position) -> Bool {
    get {
      let m = (1 as UInt) << p.offsetInBucket
      return bits[p.bucket] & m == m
    }
    set {
      setValue(newValue, for: p)
    }
  }

  /// Returns `startIndex` advanced by the given `offset`.
  public func index(at offset: Int) -> Position {
    .init(offset)
  }

  /// Returns the offset of `position` from the start of `self`.
  public func offset(of p: Position) -> Int {
    (p.bucket * UInt.bitWidth) + p.offsetInBucket
  }

  /// Accesses the element at given `offset`.
  public subscript(_ offset: Int) -> Bool {
    get { self[Position(offset)] }
    set { self[Position(offset)] = newValue }
  }

}

extension BitArray: CustomStringConvertible {

  public var description: String {
    self.map({ $0 ? "1" : "0" }).joined()
  }

}
