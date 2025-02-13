import FrontEnd
import Utils

extension Module {

  /// Inserts `end_borrow` instructions after the last use of each `access` instruction in `f`,
  /// reporting errors and warnings to `diagnostics`.
  ///
  /// - Requires: `self` is has gone through access reification. `f` is in `self`.
  public mutating func closeBorrows(in f: Function.ID, diagnostics: inout DiagnosticSet) {
    for blockToProcess in blocks(in: f) {
      for i in instructions(in: blockToProcess) {
        close(i, in: f, reportingDiagnosticsTo: &diagnostics)
      }
    }
  }

  /// If `i` is `access` or `project`, make sure it is post-dominated by respectively `end_borrow`
  /// or `end_project`, inserting new instructions as necessary; does nothing otherwise.
  private mutating func close(
    _ i: InstructionID, in f: Function.ID, reportingDiagnosticsTo log: inout DiagnosticSet
  ) {
    switch self[i] {
    case let s as Access:
      let region = extendedLiveRange(of: .register(i))

      // Delete the borrow if it's never used.
      if region.isEmpty {
        if let decl = s.binding {
          log.insert(.warning(unusedBinding: program.ast[decl].baseName, at: s.site))
        }
        removeInstruction(i)
        return
      }

      insertClose(i, atBoundariesOf: region) { (this, site) in
        EndAccess(.register(i), at: site, in: this)
      }

    case is OpenCapture:
      let region = extendedLiveRange(of: .register(i))
      insertClose(i, atBoundariesOf: region) { (this, site) in
        CloseCapture(.register(i), at: site, in: this)
      }

    case is OpenUnion:
      let region = extendedLiveRange(of: .register(i))
      insertClose(i, atBoundariesOf: region) { (this, site) in
        CloseUnion(.register(i), at: site, in: this)
      }

    case is Project:
      let region = extendedLiveRange(of: .register(i))
      insertClose(i, atBoundariesOf: region) { (this, site) in
        EndProject(.register(i), at: site, in: this)
      }

    default:
      break
    }
  }

  /// Closes the access formed by `i` at the boundaries of `region`, calling `make` to create the
  /// appropriate lifetiem closer instruction.
  ///
  /// No instruction is inserted at after already existing lifetime closers for `i`.
  private mutating func insertClose<T: LifetimeCloser>(
    _ i: InstructionID, atBoundariesOf region: Lifetime,
    makingInstructionWith make: (inout Self, SourceRange) -> T
  ) {
    for boundary in region.upperBoundaries {
      switch boundary {
      case .after(let u):
        // Skip the insertion if the last user already closes the borrow.
        if let e = self[u] as? T, e.start.instruction == i {
          continue
        }
        let s = make(&self, self[u].site)
        insert(s, after: u)

      case .start(let b):
        let site = instructions(in: b).first.map(default: self[i].site) {
          SourceRange.empty(at: self[$0].site.start)
        }
        let s = make(&self, site)
        insert(s, at: boundary)

      default:
        unreachable()
      }
    }
  }

  /// Returns the extended live-range of `definition`.
  ///
  /// A definition is *live* over an instruction if it is is used by that instruction or may be
  /// used by another instruction in the future. The live-range of a definition `d` is the region
  /// of a function containing all instructions over which `d` is live. The extended live-range of
  /// `d` is its live-range merged with the extended live-ranges of the definitions extending `d`.
  ///
  /// - Note: The definition of an operand `o` isn't part of `o`'s lifetime.
  private func extendedLiveRange(of definition: Operand) -> Lifetime {
    // Nothing to do if the operand has no use.
    guard let uses = self.uses[definition] else { return Lifetime(operand: definition) }

    // Compute the live-range of the definition.
    var r = liveRange(of: definition, definedIn: definition.block!)

    // Extend the lifetime with that of its borrows.
    for use in uses {
      switch self[use.user] {
      case is LifetimeExtender:
        if let o = result(of: use.user) {
          r = extend(lifetime: r, toCover: extendedLiveRange(of: o))
        }

      case let s as CaptureIn where use.index == 0:
        let p = provenances(s.target).uniqueElement!
        guard self[p] is AllocStack else { UNIMPLEMENTED() }
        let u = self.uses[p, default: []].first(where: { self[$0.user] is ReleaseCaptures })!
        return extend(lifetime: r, toInclude: u)

      default:
        continue
      }
    }

    return r
  }

}

extension Diagnostic {

  fileprivate static func warning(
    unusedBinding n: Identifier, at site: SourceRange
  ) -> Diagnostic {
    .warning("binding '\(n)' was never used", at: site)
  }

}

/// An instruction that extends the lifetime of all its uses.
private protocol LifetimeExtender {}

extension Access: LifetimeExtender {}

extension AdvancedByBytes: LifetimeExtender {}

extension AdvancedByStrides: LifetimeExtender {}

extension OpenCapture: LifetimeExtender {}

extension OpenUnion: LifetimeExtender {}

extension Project: LifetimeExtender {}

extension ProjectBundle: LifetimeExtender {}

extension SubfieldView: LifetimeExtender {}

extension WrapExistentialAddr: LifetimeExtender {}

/// An instruction that ends the lifetime of a borrow.
private protocol LifetimeCloser: Instruction {

  /// The lifetime being closed.
  var start: Operand { get }

}

extension RegionExit: LifetimeCloser {}
