import FrontEnd

/// Projects the address of an object.
public struct Yield: Instruction {

  /// The capability being projected.
  public let capability: AccessEffect

  /// The returned address.
  public private(set) var projection: Operand

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates a `yield` anchored at `site` that projects `a` with capability `c`.
  init(_ c: AccessEffect, _ a: Operand, at site: SourceRange, in m: Module) {
    precondition(m.type(of: a).isAddress)
    self.capability = c
    self.projection = a
    self.site = site
  }

  public var operands: [Operand] {
    [projection]
  }

  public var successors: [Block.ID] { [] }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    precondition(i == 0)
    projection = new
  }

  func replaceSuccessor(_ old: Block.ID, _ new: Block.ID) -> Bool {
    false
  }

}
