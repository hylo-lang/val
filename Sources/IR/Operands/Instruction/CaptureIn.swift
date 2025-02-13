import FrontEnd
import Utils

/// Captures and stores a remote part.
///
/// Well-formed IR guarantees the following invariants:
/// - The provenances of `target` contain a single `alloc_stack`.
/// - A `capture ... in` is post-dominated by at least one `release_captures` on the storage in
///   which it has stored an access.
public struct CaptureIn: Instruction {

  /// The operands of the instruction.
  public private(set) var operands: [Operand]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates a `capture ... in` anchored at `site` that captures `source`, which is an access, and
  /// stores it in `target`.
  public init(_ source: Operand, in target: Operand, at site: SourceRange, in m: Module) {
    precondition(m.type(of: source).isAddress)
    precondition(m.type(of: target).isAddress)
    self.operands = [source, target]
    self.site = site
  }

  /// The captured remote part.
  public var source: Operand { operands[0] }

  /// The location at which the remote part is stored.
  public var target: Operand { operands[1] }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    operands[i] = new
  }

}

extension CaptureIn: CustomStringConvertible {

  public var description: String {
    "capture \(source) in \(target)"
  }

}
