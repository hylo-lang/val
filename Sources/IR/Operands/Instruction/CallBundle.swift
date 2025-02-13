import FrontEnd
import Utils

/// Invokes one variant of `bundle` with `arguments` and writes its result to `output`.
public struct CallBundle: Instruction {

  /// The method bundle implementing the variant to call.
  public let bundle: BundleReference<MethodDecl>

  /// The type of the bundle.
  public let bundleType: MethodType

  /// The variants of the bundle.
  public let variants: [AccessEffect: Function.ID]

  /// The return storage and arguments of the call.
  public private(set) var operands: [Operand]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates a `call_bundle` that applies one of the variants defined in `m` to arguments `a`,
  /// canonicalizing types in `scopeOfUse`.
  public init(
    applying m: BundleReference<MethodDecl>,
    to a: [Operand],
    writingResultTo o: Operand,
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
    precondition(variants.count > 1)

    let t = MethodType(
      module.program.canonicalType(of: m.bundle, specializedBy: m.arguments, in: scopeOfUse))!
    precondition((t.inputs.count + 1) == a.count)
    precondition(a.allSatisfy({ module[$0] is Access }))
    precondition(module.isBorrowSet(o))

    self.bundle = m
    self.bundleType = t
    self.variants = variants
    self.operands = [o] + a
    self.site = site
  }

  /// The capabilities possibly requested on the receiver.
  public var capabilities: AccessEffectSet {
    .init(variants.keys)
  }

  /// The location at which the result of `callee` is stored.
  public var output: Operand { operands[0] }

  /// The arguments of the call.
  public var arguments: ArraySlice<Operand> { operands[1...] }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    operands[i] = new
  }

}

extension CallBundle: CustomStringConvertible {

  public var description: String {
    "call_bundle \(capabilities) \(bundle)(\(list: arguments)) to \(output)"
  }

}

