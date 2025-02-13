import FrontEnd
import Utils

/// Exposes a captured access.
public struct OpenCapture: RegionEntry {

  public typealias Exit = CloseCapture

  /// The type of the address being loaded.
  public let result: IR.`Type`?

  /// The operands of the instruction.
  public private(set) var operands: [Operand]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates an `open_capture` anchored at `site` that loads the address stored at `source`.
  public init(_ source: Operand, at site: SourceRange, in m: Module) {
    let t = RemoteType(m.type(of: source).ast) ?? preconditionFailure()
    self.result = .address(t.bareType)
    self.operands = [source]
    self.site = site
  }

  /// The location of the storage containing the address to load.
  public var source: Operand {
    operands[0]
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    operands[0] = new
  }

}
