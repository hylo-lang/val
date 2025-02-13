import FrontEnd

/// A return instruction.
public struct Return: Terminator {

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates a `return` anchored at `site`.
  init(at site: SourceRange, in module: Module) {
    self.site = site
  }

  public var successors: [Block.ID] { [] }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    preconditionFailure()
  }

  func replaceSuccessor(_ old: Block.ID, with new: Block.ID) -> Bool {
    false
  }

}
