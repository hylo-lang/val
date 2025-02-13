import FrontEnd
import Utils

/// Invokes `callee` with `arguments` and writes its result to `output`.
///
/// `callee` must have a lambda type; the type of the instruction must be the same as output type
/// of the callee. `operands` must contain as many operands as the callee's type.
public struct Call: Instruction {

  /// The callee, the return storage, and arguments of the call.
  public private(set) var operands: [Operand]

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange

  /// Creates a `call` anchored at `site` that applies `callee` on `arguments` and writes its
  /// result to `output`.
  public init(
    applying callee: Operand,
    to arguments: [Operand],
    writingResultTo output: Operand,
    at site: SourceRange,
    in m: Module
  ) {
    let t = ArrowType(m.type(of: callee).ast)!.strippingEnvironment
    precondition(t.inputs.count == arguments.count)
    precondition(arguments.allSatisfy({ m[$0] is Access }))
    precondition(m.isBorrowSet(output))

    self.operands = [callee, output] + arguments
    self.site = site
  }

  /// The callee.
  public var callee: Operand { operands[0] }

  /// The location at which the result of `callee` is stored.
  public var output: Operand { operands[1] }

  /// The arguments of the call.
  public var arguments: ArraySlice<Operand> { operands[2...] }

  /// `true` iff the instruction denotes a call to a generic function.
  public var isGeneric: Bool {
    if let f = callee.constant as? FunctionReference {
      return !f.specialization.isEmpty
    } else {
      return false
    }
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    operands[i] = new
  }

}

extension Call: CustomStringConvertible {

  public var description: String {
    "call \(callee)(\(list: arguments)) to \(output)"
  }

}
