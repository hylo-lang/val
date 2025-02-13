import FrontEnd

/// Projects a value from a subscript bundle.
public struct ProjectBundle: Instruction {

  /// The subscript bundle implementing the projections.
  public let bundle: BundleReference<SubscriptDecl>

  /// The parameters of the subscript.
  public let parameters: [ParameterType]

  /// The type of the projected value.
  public let projection: AnyType

  /// The subscripts implementing the projection.
  public let variants: [AccessEffect: Function.ID]

  /// The arguments of the call.
  ///
  /// Operands to must be the result of an `access` instruction requesting a capability for each
  /// variant in `callee` and having no use before `project_bundle`.
  public private(set) var operands: [Operand]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates a `project_bundle` that applies one of the variants defined in `m` to arguments `a`,
  /// canonicalizing types in `scopeOfUse`.
  public init(
    applying m: BundleReference<SubscriptDecl>,
    to a: [Operand],
    at site: SourceRange,
    in module: inout Module,
    canonicalizingTypesIn scopeOfUse: AnyScopeID
  ) {
    var variants: [AccessEffect: Function.ID] = [:]
    for v in module.program[m.bundle].impls {
      let i = module.program[v].introducer.value
      if m.capabilities.contains(i) {
        variants[i] = module.demandDeclaration(lowering: v)
      }
    }
    precondition(!variants.isEmpty)

    let t = SubscriptType(
      module.program.canonicalType(of: m.bundle, specializedBy: m.arguments, in: scopeOfUse))!.pure

    self.bundle = m
    self.variants = variants
    self.parameters = t.inputs.lazy.map({ ParameterType($0.type)! })
    self.projection = RemoteType(t.output)!.bareType
    self.operands = a
    self.site = site
  }

  /// The capabilities of the projected value.
  public var capabilities: AccessEffectSet {
    .init(variants.keys)
  }

  /// The types of the instruction's results.
  public var result: IR.`Type`? {
    .address(projection)
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    operands[i] = new
  }

}

extension ProjectBundle: CustomStringConvertible {

  public var description: String {
    if operands.isEmpty {
      return "project_bundle \(capabilities) \(bundle)"
    } else {
      return "project_bundle \(capabilities) \(bundle), \(list: operands)"
    }
  }

}
