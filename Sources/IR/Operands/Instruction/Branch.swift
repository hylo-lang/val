import FrontEnd

/// Branches unconditionally to the start of a basic block.
public struct Branch: Terminator {

  /// The target of the branch.
  public private(set) var target: Block.ID

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an instance with the given properties.
  fileprivate init(target: Block.ID, site: SourceRange) {
    self.target = target
    self.site = site
  }

  public var successors: [Block.ID] { [target] }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    preconditionFailure()
  }

  mutating func replaceSuccessor(_ old: Block.ID, with new: Block.ID) -> Bool {
    precondition(new.function == target.function)
    if target == old {
      target = new
      return true
    } else {
      return false
    }
  }

}

extension Branch: CustomStringConvertible {

  public var description: String {
    "branch \(target)"
  }

}

extension Branch {

  /// Creates a `branch` anchored at `site` that unconditionally jumps at the start of a block.
  ///
  /// - Parameters:
  ///   - target: The block in which control flow jumps.
  init(to target: Block.ID, at anchor: SourceRange, in m: Module) {
    self.init(target: target, site: anchor)
  }

}
