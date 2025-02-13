import FrontEnd

/// Projects the address of a union payload, viewed as an instance of a given type.
public struct OpenUnion: RegionEntry {

  public typealias Exit = CloseUnion

  /// The union whose payload should be projected.
  ///
  /// `container` must denote the address of a union instance and there shouldn't be used by any
  /// other live `open_union` instruction.
  public private(set) var container: Operand

  /// The type of the projected payload.
  ///
  /// `payloadType` must be element of `container`'s storage type. If `payloadType.access`
  public let payloadType: AnyType

  /// `true` iff the projected address is used to initializer `container`'s storage.
  ///
  /// If this property's `true`, `container` must refer to uninitialized storage. Otherwise, it
  /// must refer to initialized storage.
  public let isUsedForInitialization: Bool

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an `open_union` anchored at `site` that projects the address of `container`'s payload
  /// viewed as an instance of `payload`.
  ///
  /// If the bits of the union's discriminator are hidden in its storage, this function removes
  /// them before projecting the address unless `isUsedForInitialization` is `true`.
  public init(
    _ container: Operand, as payload: AnyType,
    forInitialization isUsedForInitialization: Bool = false,
    at site: SourceRange, in m: Module
  ) {
    precondition(m.type(of: container).isAddress)
    precondition(payload.isCanonical)
    self.container = container
    self.payloadType = payload
    self.isUsedForInitialization = isUsedForInitialization
    self.site = site
  }

  public var result: IR.`Type`? {
    .address(payloadType)
  }

  public var operands: [Operand] {
    [container]
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    precondition(i == 0)
    container = new
  }

}

extension OpenUnion: CustomStringConvertible {

  public var description: String {
    if isUsedForInitialization {
      return "open_union [set] \(container) as \(payloadType)"
    } else {
      return "open_union \(container) as \(payloadType)"
    }
  }

}
