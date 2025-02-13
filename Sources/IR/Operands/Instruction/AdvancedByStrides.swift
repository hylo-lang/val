import FrontEnd

/// Computes a `source` address advanced by `count` strides of its referred type.
///
/// The stride of a type is the number of bytes from the start of an instance to the start of the
/// next when stored in contiguous memory.
public struct AdvancedByStrides: Instruction {

  /// The address to be advanced.
  public private(set) var base: Operand

  /// The number of strides by which to advance the source value.
  public let offset: Int

  /// The type of the instruction's result.
  public let result: IR.`Type`?

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an `advanced by strides` instruction anchored at `site` computing the `source`
  /// address advanced by `n` strides of its referred type.
  public init(
    _ source: Operand,
    offset n: Int,
    at site: SourceRange,
    in m: Module
  ) {
    guard let b = m.sourceType(source) else {
      preconditionFailure("source must be the address of a buffer")
    }
    self.base = source
    self.offset = n
    self.result = .address(b.element)
    self.site = site
  }

  public var operands: [Operand] {
    [base]
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    precondition(i == 0)
    base = new
  }

}

extension AdvancedByStrides: CustomStringConvertible {

  public var description: String {
    "\(base) advanced by \(offset) strides"
  }

}

extension Module {

  /// Returns the AST type of `source` iff it is the address of a buffer.
  fileprivate func sourceType(_ source: Operand) -> BufferType? {
    let s = type(of: source)
    if s.isAddress {
      return BufferType(s.ast)
    } else {
      return nil
    }
  }

}
