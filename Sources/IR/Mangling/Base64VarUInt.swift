/// An unsigned integer whose textual representation uses a variable-length code in base 64.
///
/// The textual representation of a `Base64VarUInt` is satisfies the following properties:
/// * Small values use fewer characters than larger values.
/// * The length of the representation can be determined by looking at just the first character.
///
/// The textual representation of `v` is composed of 1 to `n` ASCII characters (`0 < n < 12`),
/// written `an`. `v` is decoded as follows:
/// - If `a0 < 51`, then `n = 1` and `v = a0`.
/// - If `a0 == 51`, then `n = 2` and `v = 50 + a1`.
/// - If `a0 == 52`, then `n = 3` and `v = 114 + 64 * a1 + a2`.
/// - Otherwise, `n = a0` and `v` is the sum of `ai * 64^(a0 - i)` for `1 <= i < a0`.
public struct Base64VarUInt: Hashable {

  /// The value of the digit, in the range `0 ..< UInt64.max`.
  public let rawValue: UInt64

  /// Creates an instance from its.
  ///
  /// - Requires: `n >= 0`
  public init<T: BinaryInteger>(_ n: T) {
    self.rawValue = UInt64.init(n)
  }

}

extension Base64VarUInt: RawRepresentable {

  /// Creates an instance from its raw value.
  public init(rawValue n: UInt64) {
    self.init(n)
  }

}

extension Base64VarUInt: Comparable {

  /// Returns `true` iff `l` is less than `r`.
  public static func < (l: Self, r: Self) -> Bool {
    l.rawValue < r.rawValue
  }

}

extension Base64VarUInt: TextOutputStreamable {

  public func write<T: TextOutputStream>(to output: inout T) {
    if rawValue < 51 {
      output.write(Base64Digit(rawValue)!.description)
      return
    } else if rawValue < 115 {
      output.write(Base64Digit(51)!.description)
      output.write(Base64Digit(rawValue - 51)!.description)
    } else if rawValue < 4210 {
      let m = rawValue - 114
      output.write(Base64Digit(52)!.description)
      output.write(Base64Digit(m / 64)!.description)
      output.write(Base64Digit(m % 64)!.description)
    } else {
      var digits: [Base64Digit] = []
      digits.reserveCapacity(11)

      var m = rawValue - 4209
      assert(m > 0)
      while m > 0 {
        digits.append(Base64Digit(m % 64)!)
        m /= 64
      }

      output.write(Base64Digit(52 + digits.count)!.description)
      for d in digits.reversed() {
        output.write(d.description)
      }
    }
  }

}

extension Base64VarUInt: LosslessStringConvertible {

  public init?(_ description: String) {
    guard
      let (d, i) = Self.decode(from: description),
      i == description.endIndex
    else { return nil }
    self = d
  }

  public var description: String {
    var s = ""
    write(to: &s)
    return s
  }

  /// Parses an instance at the beginning of the given string, returning its value and the position
  /// immediately after the last character of the decoded value's representation.
  public static func decode<S: StringProtocol>(
    from input: S
  ) -> (decoded: Base64VarUInt, indexAfter: S.Index)? {
    guard let (d, c) = decode(from: input.utf8) else {
      return nil
    }
    return (decoded: d, indexAfter: input.index(input.startIndex, offsetBy: c))
  }

  /// Parses an instance at the beginning of the given byte sequence, returning its value and the
  /// number of bytes read.
  public static func decode<S: Sequence<UInt8>>(
    from stream: S
  ) -> (decoded: Base64VarUInt, readCount: Int)? {
    var i = stream.makeIterator()
    func digit() -> Base64Digit? {
      i.next().flatMap(Base64Digit.init(ascii:))
    }

    guard let a0 = digit() else {
      return nil
    }

    if a0.rawValue < 51 {
      return (decoded: Base64VarUInt(a0.rawValue), readCount: 1)
    }

    if a0.rawValue == 51 {
      guard let a1 = digit() else {
        return nil
      }
      let n = 51 + UInt64(a1.rawValue)
      return (decoded: Base64VarUInt(n), readCount: 2)
    }

    if a0.rawValue == 52 {
      guard let a1 = digit(), let a2 = digit() else {
        return nil
      }
      let n: UInt64 = 114 + (64 * UInt64(a1.rawValue)) + UInt64(a2.rawValue)
      return (decoded: Base64VarUInt(n), readCount: 3)
    }

    let digitCount = Int(a0.rawValue) - 52
    var digits: [Base64Digit] = []
    digits.reserveCapacity(digitCount)

    for _ in 0..<digitCount {
      guard let ai = digit() else { return nil }
      digits.append(ai)
    }

    var n: UInt64 = 4209
    var m: UInt64 = 1
    for d in digits.reversed() {
      n += m * UInt64(d.rawValue)
      m *= 64
    }

    return (decoded: Base64VarUInt(n), readCount: 1 + digitCount)
  }

}
