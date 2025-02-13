import FrontEnd

/// Projects a value.
public struct Project: RegionEntry {

  public typealias Exit = EndProject

  /// The type of the projected value.
  public let projection: RemoteType

  /// The subscript implementing the projection.
  public let callee: Function.ID

  /// If `callee` is generic, the arguments to its generic parameter.
  public let specialization: GenericArguments

  /// The arguments of the call.
  ///
  /// Operands to non-`sink` inputs must be the result of a `borrow` instruction requesting the
  /// same capability as `projection.access` and having no use before `project`.
  public private(set) var operands: [Operand]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an instance with the given properties.
  fileprivate init(
    projection: RemoteType,
    callee: Function.ID,
    specialization: GenericArguments,
    operands: [Operand],
    site: SourceRange
  ) {
    self.projection = projection
    self.callee = callee
    self.specialization = specialization
    self.operands = operands
    self.site = site
  }

  /// The types of the instruction's results.
  public var result: IR.`Type`? {
    .address(projection.bareType)
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    operands[i] = new
  }

}

extension Project: CustomStringConvertible {

  public var description: String {
    if operands.isEmpty {
      return "project \(callee)"
    } else {
      return "project \(callee), \(list: operands)"
    }
  }

}

extension Project {

  /// Creates a `project` anchored at `site` that projects a value of type `t` by applying `s`,
  /// which is a reference to a lowered subscript, on `arguments`.
  init(
    _ t: RemoteType, applying s: FunctionReference, to arguments: [Operand], at site: SourceRange,
    in m: Module
  ) {
    self.init(
      projection: t, callee: s.function, specialization: s.specialization,
      operands: arguments, site: site)
  }

  /// Creates a `project` anchored at `site` that projects a value of type `t` by applying `s`,
  /// which is a lowered subscript, specialized by `z`, on `arguments`.
  init(
    _ t: RemoteType, applying s: Function.ID, specializedBy z: GenericArguments,
    to arguments: [Operand], at site: SourceRange, in m: Module
  ) {
    self.init(projection: t, callee: s, specialization: z, operands: arguments, site: site)
  }

}
