import FrontEnd

/// Branches to one of several basic blocks.
public struct Switch: Terminator {

  /// An index in `successors` expressed as a built-in integer value.
  public private(set) var index: Operand

  /// The possible targets of the instruction.
  public private(set) var successors: [Block.ID]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an instance with the given properties.
  fileprivate init(index: Operand, successors: [Block.ID], site: SourceRange) {
    self.index = index
    self.successors = successors
    self.site = site
  }

  public var operands: [Operand] {
    [index]
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    precondition(i == 0)
    index = new
  }

  mutating func replaceSuccessor(_ old: Block.ID, with new: Block.ID) -> Bool {
    precondition(new.function == successors[0].function)
    for i in 0..<successors.count {
      if successors[i] == old {
        successors[i] = new
        return true
      }
    }
    return false
  }

}

extension Switch: CustomStringConvertible {

  public var description: String {
    "switch \(index), \(list: successors)"
  }

}

extension Module {

  /// Creates a `switch` anchored at `site` that jumps to `successors[i]`.
  ///
  /// - Requires: `i` is a valid index in `successors`, expressed as a built-in integer, and
  ///   `successors` is not empty.
  func makeSwitch(
    on index: Operand, toOneOf successors: [Block.ID], at site: SourceRange
  ) -> Switch {
    let t = type(of: index)
    precondition(t.isObject && t.ast.isBuiltinInteger)
    precondition(!successors.isEmpty)

    return .init(index: index, successors: successors, site: site)
  }

}
