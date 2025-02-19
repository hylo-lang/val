extension FixedWidthInteger where Self: UnsignedInteger {

  /// The number of bytes needed to hold `self` bits.
  public var bitsToBytes: UInt {
    (UInt(self) + 7) / 8
  }

  /// The number of bits in `self` bytes.
  public var bytesToBits: UInt {
    UInt(self) * 8
  }

  /// The number of bits required to represent `self`.
  public var bitsInRepresentation: UInt {
    UInt(MemoryLayout.size(ofValue: self)).bytesToBits - UInt(self.leadingZeroBitCount)
  }

  /// The minimum bit width of an
  public var minimumUnsignedIntegerTypeBits: UInt {
    Swift.max(8, bitsInRepresentation.roundedUpToPowerOf2)
  }

  public var roundedUpToPowerOf2: UInt {
    self == 0 ? 1 : 1 << (self - 1).bitsInRepresentation
  }
}
