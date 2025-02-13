import FrontEnd

/// Computes the address of storage for a field or sub-field of a record, given the record's address.
///
/// Does not access memory.
public struct SubfieldView: Instruction {

  /// The address of the whole record.
  public private(set) var recordAddress: Operand

  /// The subfield of the whole record whose address is computed.
  public let subfield: RecordPath

  /// The type of the resulting address.
  public let resultType: IR.`Type`

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange


  /// Creates a `subfield_view` anchored at `site` computing the address of the given `subfield` of
  /// some record at `recordAddress`.
  init(
    of recordAddress: Operand, subfield elementPath: RecordPath,
    at site: SourceRange, in module: Module
  ) {
    precondition(module.type(of: recordAddress).isAddress)
    let l = AbstractTypeLayout(of: module.type(of: recordAddress).ast, definedIn: module.program)
    let t = l[elementPath].type
    self.recordAddress = recordAddress
    self.subfield = elementPath
    self.resultType = .address(t)
    self.site = site
  }

  public var result: IR.`Type`? {
    resultType
  }

  public var operands: [Operand] {
    [recordAddress]
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    precondition(i == 0)
    recordAddress = new
  }

}

extension SubfieldView: CustomStringConvertible {

  public var description: String {
    "subfield_view \(recordAddress)\(subfield.isEmpty ? "" : ", ")\(list: subfield)"
  }

}
