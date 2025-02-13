import FrontEnd

extension Module {

  /// Replace occurrences of `call_bundle` by `call` depending on the uses of their first operands,
  /// reporting errors and warnings to `diagnostics`.
  ///
  /// - Requires: `f` is in `self`.
  public mutating func reifyCallsToBundles(in f: Function.ID, diagnostics: inout DiagnosticSet) {
    for i in blocks(in: f).map(instructions(in:)).joined() where self[i] is CallBundle {
      reify(callBundle: i)
    }
  }

  private mutating func reify(callBundle i: InstructionID) {
    let s = self[i] as! CallBundle
    let k = s.capabilities.weakest!

    var arguments = Array(s.arguments)
    let r = Access(k, from: arguments[0], at: s.site, in: self)
    arguments[0] = .register(insert(r, before: i))

    let b = Block.ID(containing: i)
    let f = FunctionReference(
      to: s.variants[k]!, in: self, specializedBy: s.bundle.arguments, in: self[b].scope)

    let reified = Call(
      applying: .constant(f), to: arguments, writingResultTo: s.output, at: s.site, in: self)
    replace(i, with: reified)
  }

}
