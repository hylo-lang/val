import FrontEnd

/// Copies the memory representation of the value stored `source` to `target`.
public struct MemoryCopy: Instruction {

  /// The operands of the instruction.
  public private(set) var operands: [Operand]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an `memory_copy` anchored at `site` that copies the memory representation of the
  /// value stored at `source` to `target`.
  ///
  /// - Requires: `source` is a `let`-capable access and `target` is a `set`-capable access.
  ///   `source` and `target` have the same type.
  public init(_ source: Operand, _ target: Operand, at site: SourceRange, in m: Module) {
    let s = m.type(of: source)
    precondition(s.isAddress && (s == m.type(of: target)))
    self.operands = [source, target]
    self.site = site
  }

  /// The storage from which bytes are read.
  public var source: Operand { operands[0] }

  /// The storage to which bytes are written.
  public var target: Operand { operands[1] }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    operands[i] = new
  }

}
