import FrontEnd
import OrderedCollections

/// Branches to one of several basic blocks based on the discriminator of a union.
public struct UnionSwitch: Terminator {

  /// The type of a map from payload type to its target.
  public typealias Targets = OrderedDictionary<AnyType, Block.ID>

  /// The discriminator of the union container over which the instruction switches.
  public private(set) var discriminator: Operand

  /// The type of the union over which the instruction switches.
  public let union: UnionType

  /// A map from payload type to its target.
  public private(set) var targets: Targets

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an instance with the given properties.
  fileprivate init(discriminator: Operand, union: UnionType, targets: Targets, site: SourceRange) {
    self.discriminator = discriminator
    self.union = union
    self.targets = targets
    self.site = site
  }

  public var operands: [Operand] {
    [discriminator]
  }

  public var successors: [Block.ID] {
    Array(targets.values)
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    precondition(i == 0)
    discriminator = new
  }

  mutating func replaceSuccessor(_ old: Block.ID, with new: Block.ID) -> Bool {
    precondition(new.function == successors[0].function)
    for (t, b) in targets {
      if b == old {
        targets[t] = b
        return true
      }
    }
    return false
  }

}

extension UnionSwitch: CustomStringConvertible {

  public var description: String {
    var s = "union_switch \(discriminator)"
    for (t, b) in targets {
      s.write(", \(t) => \(b)")
    }
    return s
  }

}

extension Module {

  /// Creates a `union_switch` anchored at `site` that switches over `discriminator`, which is the
  /// discriminator of a container of type `union`, jumping to corresponding block in `target`.
  ///
  /// If `union` is generic, `discriminator` should be the result of `union_discriminator` rather
  /// than a constant.
  ///
  /// - Requires: `targets` has a key defined for each of `union`.
  func makeUnionSwitch(
    over discriminator: Operand, of union: UnionType, toOneOf targets: UnionSwitch.Targets,
    at site: SourceRange
  ) -> UnionSwitch {
    let t = type(of: discriminator)
    precondition(t.isObject && t.ast.isBuiltinInteger)
    precondition(union.elements.allSatisfy({ (e) in targets[e] != nil }))
    return .init(discriminator: discriminator, union: union, targets: targets, site: site)
  }

}
