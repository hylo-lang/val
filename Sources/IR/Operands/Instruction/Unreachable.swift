import FrontEnd

/// Marks this execution path as unreachable, causing a fatal error otherwise.
public struct Unreachable: Terminator {

  /// The site of the code corresponding to that instruction.
  public var site: SourceRange

  /// Creates an instance in `m` with the given properties.
  init(at site: SourceRange, in m: Module) {
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
