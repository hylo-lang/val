import FrontEnd

/// Deallocates memory previously allocated by `alloc_stack`.
public struct DeallocStack: Instruction {

  /// The location of the memory being deallocated.
  public private(set) var location: Operand

  /// The site of the code corresponding to that instruction.
  public let site: SourceRange


  /// Creates a `dealloc_stack` anchored at `site` that deallocates memory allocated by `alloc`.
  ///
  /// - Parameters:
  ///   - alloc: The address of the memory to deallocate. Must be the result of `alloc`.
  public init(for alloc: Operand, at site: SourceRange, in m: Module) {
    precondition(alloc.instruction.map({ m[$0] is AllocStack }) ?? false)
    self.location = alloc
    self.site = site
  }

  public var operands: [Operand] {
    [location]
  }

  public mutating func replaceOperand(at i: Int, with new: Operand) {
    precondition(i == 0)
    location = new
  }

}
