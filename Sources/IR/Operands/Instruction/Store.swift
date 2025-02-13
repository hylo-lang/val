import FrontEnd

/// Stores `object` at the specified location.
public struct Store: Instruction {

  /// The object to store.
  public private(set) var object: Operand

  /// The location at which the object is stored.
  public private(set) var target: Operand

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates a `store` anchored at `site` that stores `object` at `target`.
  ///
  /// - Parameters:
  ///   - object: The object to store. Must have an object type.
  ///   - target: The location at which `object` is stored. Must have an address type.
  init(_ object: Operand, at target: Operand, at site: SourceRange, in module: Module) {
    precondition(module.type(of: object).isObject)
    precondition(module.type(of: target).isAddress)
    self.object = object
    self.target = target
    self.site = site
  }

  public var operands: [Operand] {
    [object, target]
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    switch i {
    case 0: object = new
    case 1: target = new
    default:
      preconditionFailure()
    }
  }

}
