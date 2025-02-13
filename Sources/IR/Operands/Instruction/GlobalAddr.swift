import FrontEnd

/// Returns the address of a global binding.
public struct GlobalAddr: Instruction {

  /// The ID of the global global binding to access.
  public let binding: BindingDecl.ID

  /// The type of the binding value.
  public let valueType: AnyType

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an `global_addr` anchored at `site` that returns the address of `binding`.
  public init(of binding: BindingDecl.ID, at anchor: SourceRange, in m: Module) {
    let b = m.program[binding]
    let t = m.program.canonical(b.type, in: b.scope)
    self.binding = binding
    self.valueType = t
    self.site = anchor
  }

  public var result: IR.`Type`? {
    .address(valueType)
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    preconditionFailure()
  }

}

extension GlobalAddr: CustomStringConvertible {

  public var description: String {
    "global_addr @\(binding)"
  }

}
