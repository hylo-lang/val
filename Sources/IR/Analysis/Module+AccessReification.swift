import DequeModule
import FrontEnd
import Utils

/// Implementation notes
/// ====================
///
/// This transformation pass implements the following algorithm:
///
/// 1. Gather all reifiable access instructions in the function in a set `W`.
/// 2. While an instruction `i` can be popped from `W`:
///   a. Initialize a set `R` with the weakest capability offered by `i`.
///   b. Gather the requested capabilities on `i` from all its uses into `R`.
///   c. If `R` is the singleton `{k}`, reify `i` as an access providing just `k`. Otherwise,
///      insert `i` back into `W`.
///   d. Go back to step 2.
///
/// The algorithm converges because a reifiable `i` is put back into `W` if and only if all its
/// uses are other reifiable accesses. Since a definition cannot use itself, dependencies between
/// reifiable accesses form a forest whose leaves do not have reifiable user. Iterating over the
/// elements in `W` eliminates those leaves, forming a smaller forest until `W` is empty.
///
/// Step 2b is implemented by `Module.forEachClient(of:)` and `Module.requests(_:)`. The former
/// iterates over all the uses of an instruction, traversing instructions that compute derived
/// addresses (.e.g., `subfield_view`). The latter returns the set of requested capabilities for
/// each user. As well-formed accesses to memory must be done via `access`, there's a fairly small
/// number of instructions to consider.
///
/// Note that `move` are assumed to request `inout` only as assignment should be preferred over
/// initialization. This assumption is sound because if the reifiable access only provides `set`,
/// then `move` will be rewritten as initialization during the DI pass.

extension Module {

  /// Replace uses of instructions requesting multiple capabilities by one requesting the weakest
  /// actually required, reporting errors and warnings to `diagnostics`.
  ///
  /// - Requires: `f` is in `self`.
  public mutating func reifyAccesses(in f: Function.ID, diagnostics: inout DiagnosticSet) {
    var work: Deque<InstructionID> = []
    for i in blocks(in: f).map(instructions(in:)).joined() {
      guard let s = self[i] as? ReifiableAccess else { continue }

      // Fast path if the request set is already a singleton.
      if let k = s.capabilities.uniqueElement {
        reify(i, as: k)
        continue
      }

      // Algorithm assumes no access or projection can offer `set` and `let` without also offering
      // `inout` so that `move` instructions can be treated as though they only requested `inout`.
      let k = s.capabilities
      precondition(!k.isSuperset(of: [.set, .let]) || k.contains(.inout))
      work.append(i)
    }

    while let i = work.popFirst() {
      let s = self[i] as! ReifiableAccess
      let available = s.capabilities
      assert(!available.isSingleton, "access already reified")

      var lower = AccessEffect.let
      var upper = AccessEffect.let

      forEachClient(of: i) { (u) in
        let rs = requests(u)
        if let w = rs.weakest { lower = max(w, lower) }
        upper = rs.strongest(including: upper)
      }

      if lower == upper {
        // We have to "promote" a request if it can be satisfied by a stronger capability.
        let k = available.elements.first(where: { (a) in a >= lower }) ?? available.weakest!
        reify(i, as: k)
      } else {
        work.append(i)
      }
    }
  }

  private func requests(_ u: Use) -> AccessEffectSet {
    switch self[u.user] {
    case let t as Access:
      return t.capabilities
    case is Load:
      return [.sink]
    case is Move:
      return u.index == 0 ? [.sink] : [.inout]
    case is ProjectBundle:
      return requests(projectBundle: u)
    default:
      return []
    }
  }

  private func requests(projectBundle u: Use) -> AccessEffectSet {
    let s = self[u.user] as! ProjectBundle
    let t = s.parameters[u.index]
    return (t.access == .yielded) ? s.capabilities : [t.access]
  }

  /// Calls `action` on the uses of a capability of the access at the origin of `i`.
  private func forEachClient(of i: InstructionID, _ action: (Use) -> Void) {
    for u in allUses(of: i) {
      if self[u.user].isTransparentOffset {
        forEachClient(of: u.user, action)
      } else {
        action(u)
      }
    }
  }

  /// Replaces the uses of `i` with uses of an instruction providing the same access but only
  /// with capability `k`.
  private mutating func reify(_ i: InstructionID, as k: AccessEffect) {
    switch self[i] {
    case is Access:
      reify(access: i, as: k)
    case is ProjectBundle:
      reify(projectBundle: i, as: k)
    default:
      unreachable()
    }
  }

  /// Narrows the capabilities requested by `i`, which is an `access` instruction, to just `k`.
  private mutating func reify(access i: InstructionID, as k: AccessEffect) {
    let s = self[i] as! Access
    assert(s.capabilities.contains(k))

    // Nothing to do if the request set is already a singleton.
    if s.capabilities == [k] { return }

    let reified = Access(k, from: s.source, correspondingTo: s.binding, at: s.site, in: self)
    replace(i, with: reified)
  }

  private mutating func reify(projectBundle i: InstructionID, as k: AccessEffect) {
    let s = self[i] as! ProjectBundle
    assert(s.capabilities.contains(k))

    // Generate the proper instructions to prepare the projection's arguments.
    var arguments = s.operands
    for a in arguments.indices where s.parameters[a].access == .yielded {
      let b = Access(k, from: arguments[a], at: s.site, in: self)
      arguments[a] = .register(insert(b, before: i))
    }

    let o = RemoteType(k, s.projection)
    let reified = Project(
      o, applying: s.variants[k]!, specializedBy: s.bundle.arguments, to: arguments, at: s.site,
      in: self)
    replace(i, with: reified)
  }

}

/// An instruction denoting an access that may be refiable.
private protocol ReifiableAccess {

  /// The capabilities available on the access.
  var capabilities: AccessEffectSet { get }

}

extension Access: ReifiableAccess {}

extension ProjectBundle: ReifiableAccess {}

extension Instruction {

  /// `true` iff `self` is an instruction computing an address derived from its operand without
  /// accessing them.
  fileprivate var isTransparentOffset: Bool {
    switch self {
    case is AdvancedByStrides:
      return true
    case is OpenCapture:
      return true
    case is OpenUnion:
      return true
    case is SubfieldView:
      return true
    case is WrapExistentialAddr:
      return true
    default:
      return false
    }
  }

}
