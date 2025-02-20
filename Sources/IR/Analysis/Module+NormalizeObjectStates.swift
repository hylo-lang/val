import DequeModule
import FrontEnd
import Utils

extension Module {

  /// A "program counter" in the abstract machine.
  private typealias PC = Block.Instructions.Address

  /// Ensures that objects in `f` are initialized before use and deinitialized after last use,
  /// reporting errors and warnings to `diagnostics`.
  ///
  /// - Requires: Borrows in `self` have been closed. `f` is in `self`.
  public mutating func normalizeObjectStates(in f: Function.ID, diagnostics: inout DiagnosticSet) {
    var machine = AbstractInterpreter(analyzing: f, in: self, entryContext: entryContext(of: f))

    // Verify that object states are properly initialized/deinitialized in `b` given `context`,
    // updating `self` as necessary and reporting violations in `diagnostics`.
    machine.fixedPoint { (b, context) in
      var pc = self[f][b].instructions.firstAddress
      while let a = pc {
        let user = InstructionID(f, b, a)

        switch self[f][b].instructions[a] {
        case is Access:
          pc = interpret(access: user, in: &context)
        case is AddressToPointer:
          pc = interpret(addressToPointer: user, in: &context)
        case is AdvancedByBytes:
          pc = interpret(advancedByBytes: user, in: &context)
        case is AdvancedByStrides:
          pc = interpret(advancedByStrides: user, in: &context)
        case is AllocStack:
          pc = interpret(allocStack: user, in: &context)
        case is Branch:
          pc = successor(of: user)
        case is Call:
          pc = interpret(call: user, in: &context)
        case is CallFFI:
          pc = interpret(callFFI: user, in: &context)
        case is CaptureIn:
          pc = interpret(captureIn: user, in: &context)
        case is CloseCapture:
          pc = interpret(closeCapture: user, in: &context)
        case is CloseUnion:
          pc = interpret(closeUnion: user, in: &context)
        case is CondBranch:
          pc = interpret(condBranch: user, in: &context)
        case is ConstantString:
          pc = interpret(constantString: user, in: &context)
        case is DeallocStack:
          pc = interpret(deallocStack: user, in: &context)
        case is EndAccess:
          pc = successor(of: user)
        case is EndProject:
          pc = interpret(endProject: user, in: &context)
        case is GenericParameter:
          pc = interpret(genericParameter: user, in: &context)
        case is GlobalAddr:
          pc = interpret(globalAddr: user, in: &context)
        case is CallBuiltinFunction:
          pc = interpret(callBuiltin: user, in: &context)
        case is Load:
          pc = interpret(load: user, in: &context)
        case is MarkState:
          pc = interpret(markState: user, in: &context)
        case is MemoryCopy:
          pc = interpret(memoryCopy: user, in: &context)
        case is Move:
          pc = interpret(move: user, in: &context)
        case is OpenCapture:
          pc = interpret(openCapture: user, in: &context)
        case is OpenUnion:
          pc = interpret(openUnion: user, in: &context)
        case is PointerToAddress:
          pc = interpret(pointerToAddress: user, in: &context)
        case is Project:
          pc = interpret(project: user, in: &context)
        case is ReleaseCaptures:
          pc = successor(of: user)
        case is Return:
          pc = interpret(return: user, in: &context)
        case is Store:
          pc = interpret(store: user, in: &context)
        case is SubfieldView:
          pc = interpret(subfieldView: user, in: &context)
        case is UnionDiscriminator:
          pc = interpret(unionDiscriminator: user, in: &context)
        case is UnionSwitch:
          pc = successor(of: user)
        case is Unreachable:
          pc = successor(of: user)
        case is WrapExistentialAddr:
          pc = interpret(wrapExistentialAddr: user, in: &context)
        case is Yield:
          pc = interpret(yield: user, in: &context)
        default:
          unreachable("unexpected instruction")
        }
      }
    }

    /// Returns the successor of `i`, if any.
    func successor(of i: InstructionID) -> PC? {
      self[i.function][i.block].instructions.address(after: i.address)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(access i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! Access
      precondition(s.source.constant == nil, "source is a constant")

      // Access is expected to be reified at this stage.
      let request = s.capabilities.uniqueElement!

      // Operand must be a location; objects at each location have the same state unless DI or LoE
      // has been broken, in which case we can assume an error has been/will be diagnosed.
      let locations = context.locals[s.source]!.unwrapLocations()!
      var o = context.withObject(at: locations.first!, { $0 })

      switch request {
      case .let, .inout, .sink:
        o.value.checkInitialized(at: s.site, reportingDiagnosticsTo: &diagnostics)

      case .set:
        let p = o.value.initializedSubfields
        if p.isEmpty { break }

        insertDeinit(
          s.source, at: p, before: i,
          anchoringInstructionsTo: s.site, reportingDiagnosticsTo: &diagnostics)
        o.value = .full(.uninitialized)
        context.forEachObject(at: s.source, { $0 = o })

      case .yielded:
        unreachable()
      }

      context.locals[.register(i)] = context.locals[s.source]
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(addressToPointer i: InstructionID, in context: inout Context) -> PC? {
      initializeRegister(createdBy: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(allocStack i: InstructionID, in context: inout Context) -> PC? {
      // A stack leak may occur if this instruction is in a loop.
      let l = AbstractLocation.root(.register(i))
      precondition(context.memory[l] == nil, "stack leak")
      context.declareStorage(assignedTo: i, in: self, initially: .uninitialized)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(advancedByBytes i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! AdvancedByBytes
      consume(s.base, with: i, at: s.site, in: &context)
      consume(s.byteOffset, with: i, at: s.site, in: &context)
      initializeRegister(createdBy: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(advancedByStrides i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! AdvancedByStrides

      // Operand must a location.
      let locations: [AbstractLocation]
      if case .constant = s.base {
        // Operand is a constant.
        UNIMPLEMENTED()
      } else {
        locations = context.locals[s.base]!.unwrapLocations()!.map({ $0.appending([s.offset]) })
      }

      context.locals[.register(i)] = .locations(Set(locations))
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(call i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! Call
      let f = s.callee
      let callee = ArrowType(type(of: f).ast)!

      // Evaluate the callee.

      switch callee.receiverEffect {
      case .let:
        assert(f.isConstant || self[f.instruction!].isAccess(callee.receiverEffect))
      case .inout:
        assert(self[f.instruction!].isAccess(callee.receiverEffect))
      default:
        UNIMPLEMENTED()
      }

      // Evaluate the arguments.
      for (p, a) in zip(callee.inputs, s.arguments) {
        switch ParameterType(p.type)!.access {
        case .set:
          initialize(a, in: &context)
        case .sink:
          sink(a, with: i, in: &context)
        case let request:
          assert(self[a.instruction!].isAccess(request))
        }
      }

      // Evaluate the return value.
      initialize(s.output, in: &context)

      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(callFFI i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! CallFFI
      for a in s.operands {
        consume(a, with: i, at: s.site, in: &context)
      }
      initializeRegister(createdBy: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(captureIn i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! CaptureIn
      initialize(s.target, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(closeCapture i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! CloseCapture
      let l = context.locals[s.start]!.unwrapLocations()!.uniqueElement!
      let projection = context.withObject(at: l, { $0 })

      let start = self[s.start.instruction!] as! OpenCapture
      let t = RemoteType(self.type(of: start.source).ast)!

      switch t.access {
      case .let, .inout, .set:
        for c in projection.value.consumers {
          diagnostics.insert(.error(cannotConsume: t.access, at: self[c].site))
        }

      case .sink:
        insertDeinit(
          s.start, at: projection.value.initializedSubfields, before: i,
          anchoringInstructionsTo: s.site, reportingDiagnosticsTo: &diagnostics)
        context.withObject(at: l, { $0.value = .full(.uninitialized) })

      case .yielded:
        unreachable()
      }

      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(closeUnion i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! CloseUnion
      let payload = context.locals[s.start]!.unwrapLocations()!.uniqueElement!

      // The state of the projected payload can't be partial.
      let o = context.withObject(at: payload, { $0 })
      guard case .full(let payloadInitializationState) = o.value else {
        fatalError()
      }

      // Copy the state of the payload to set the state of the container.
      let start = self[s.start.instruction!] as! OpenUnion
      context.forEachObject(at: start.container) { (o) in
        o.value = .full(payloadInitializationState)
      }

      context.memory[payload] = nil
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(condBranch i: InstructionID, in context: inout Context) -> PC? {
      let branch = self[i] as! CondBranch
      consume(branch.condition, with: i, at: branch.site, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(constantString i: InstructionID, in context: inout Context) -> PC? {
      initializeRegister(createdBy: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(deallocStack i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! DeallocStack
      let l = context.locals[s.location]!.unwrapLocations()!.uniqueElement!

      // Make sure the memory at the deallocated location is consumed or uninitialized before
      // erasing the deallocated memory from the context.
      let p = context.withObject(at: l, \.value.initializedSubfields)
      insertDeinit(
        s.location, at: p, before: i,
        anchoringInstructionsTo: s.site, reportingDiagnosticsTo: &diagnostics)
      context.memory[l] = nil
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(endProject i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! EndProject
      let r = self[s.start.instruction!] as! Project

      // TODO: Process projection arguments
      finalize(
        region: s.start, projecting: r.projection.access, from: [],
        exitedWith: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(genericParameter i: InstructionID, in context: inout Context) -> PC? {
      context.declareStorage(assignedTo: i, in: self, initially: .initialized)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(globalAddr i: InstructionID, in context: inout Context) -> PC? {
      context.declareStorage(assignedTo: i, in: self, initially: .initialized)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(callBuiltin i: InstructionID, in context: inout Context) -> PC? {
      // TODO: Check that operands are initialized.
      initializeRegister(createdBy: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(load i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! Load
      sink(s.source, with: i, in: &context)
      initializeRegister(createdBy: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(markState i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! MarkState

      // Built-in values are never consumed.
      let isBuiltin = type(of: s.storage).ast.isBuiltin

      context.forEachObject(at: s.storage) { (o) in
        if s.initialized {
          o.value = .full(.initialized)
        } else if !isBuiltin {
          // `mark_state` is treated as a consumer so that we can detect and diagnose escapes.
          o.value = .full(.consumed(by: [i]))
        }
      }

      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(memoryCopy i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! MemoryCopy
      initialize(s.target, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(move i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! Move
      let k: AccessEffect = context.isStaticallyInitialized(s.target) ? .inout : .set
      let n = Emitter.withInstance(insertingIn: &self, reportingDiagnosticsTo: &diagnostics) {
        $0.replaceMove(i, with: k)
      }
      return n.address
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(openCapture i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! OpenCapture
      let t = RemoteType(self.type(of: s.source).ast)!
      initializeRegister(createdBy: i, projecting: t, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(openUnion i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! OpenUnion
      let l = AbstractLocation.root(.register(i))
      precondition(context.memory[l] == nil, "overlapping accesses to union payload")

      // Operand must be a location.
      let locations = context.locals[s.container]!.unwrapLocations()!

      // Objects at each location have the same state unless DI or LoE has been broken.
      let o = context.withObject(at: locations.first!, { $0 })
      let t = AbstractTypeLayout(of: s.payloadType, definedIn: program)

      context.memory[l] = .init(layout: t, value: o.value)
      context.locals[.register(i)] = .locations([l])
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(pointerToAddress i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! PointerToAddress
      consume(s.source, with: i, at: s.site, in: &context)
      initializeRegister(createdBy: i, projecting: s.target, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(project i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! Project

      // TODO: Process arguments

      initializeRegister(createdBy: i, projecting: s.projection, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(return i: InstructionID, in context: inout Context) -> PC? {
      // Make sure that all non-sink parameters are initialized on exit.
      let entry = entry(of: f)!
      for (k, p) in self[f].inputs.enumerated() {
        let source = Operand.parameter(entry, k)
        if p.type.access == .sink {
          ensureUninitializedOnExit(
            source, in: &context, insertingDeinitializationBefore: i,
            reportingDiagnosticsAt: self[i].site)
        } else {
          ensureInitializedOnExit(
            source, passed: p.type.access, in: &context,
            reportingDiagnosticsAt: diagnosticSite(for: p, in: f))
        }
      }

      // Make sure that the return value is initialized on exit.
      if !self[f].isSubscript {
        ensureReturnValueIsInitialized(in: &context, at: self[i].site)
      }

      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(store i: InstructionID, in context: inout Context) -> PC? {
      let store = self[i] as! Store
      consume(store.object, with: i, at: store.site, in: &context)
      initialize(store.target, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(subfieldView i: InstructionID, in context: inout Context) -> PC? {
      let addr = self[i] as! SubfieldView

      // Operand must a location.
      let locations: [AbstractLocation]
      if case .constant = addr.recordAddress {
        // Operand is a constant.
        UNIMPLEMENTED()
      } else {
        locations =
          context.locals[addr.recordAddress]!.unwrapLocations()!.map({
            $0.appending(addr.subfield)
          })
      }

      context.locals[.register(i)] = .locations(Set(locations))
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(unionDiscriminator i: InstructionID, in context: inout Context) -> PC? {
      initializeRegister(createdBy: i, in: &context)
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(wrapExistentialAddr i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! WrapExistentialAddr
      if case .constant = s.witness {
        // Operand is a constant.
        UNIMPLEMENTED()
      }

      context.locals[.register(i)] = context.locals[s.witness]
      return successor(of: i)
    }

    /// Interprets `i` in `context`, reporting violations into `diagnostics`.
    func interpret(yield i: InstructionID, in context: inout Context) -> PC? {
      let s = self[i] as! Yield
      assert(self[s.projection.instruction!].isAccess(s.capability))
      return successor(of: i)
    }

    /// Updates `context` to mark all objects at `source`, which is an `access [.set]`, as having
    /// been fully initialized.
    func initialize(_ source: Operand, in context: inout Context) {
      assert(self[source.instruction!].isAccess(.set), "bad source")
      context.forEachObject(at: source) { (o) in
        o.value = .full(.initialized)
      }
    }

    /// Updates `context` to mark all objects at `source`, which is an `access [.sink]`, as having
    /// been consumed by `consumer`.
    func sink(_ source: Operand, with consumer: InstructionID, in context: inout Context) {
      assert(self[source.instruction!].isAccess(.sink), "bad source")

      // Built-in values are copied implicitly.
      if !type(of: source).ast.isBuiltin {
        context.forEachObject(at: source) { (o) in
          o.value = .full(.consumed(by: [consumer]))
        }
      }
    }

    /// Updates the state of the `o` in `context` to mark it has been consumed by `consumer` at
    /// `site` or reports a diagnostic explaining why `o` can't be consumed.
    func consume(
      _ o: Operand, with consumer: InstructionID, at site: SourceRange, in context: inout Context
    ) {
      // Constant values are synthesized on demand. Built-ins are never consumed.
      if case .constant = o { return }
      if type(of: o).ast.isBuiltin { return }

      var v = context.locals[o]!.unwrapObject()!
      if v.value == .full(.initialized) {
        v.value = .full(.consumed(by: [consumer]))
        context.locals[o]! = .object(v)
      } else {
        diagnostics.insert(.illegalMove(at: site))
      }
    }

    /// Checks that entry parameter `p`, passed with capability `k`, is initialized in `context`,
    /// reporting diagnostics at `site` if it isn't.
    func ensureInitializedOnExit(
      _ p: Operand, passed k: AccessEffect, in context: inout Context,
      reportingDiagnosticsAt site: SourceRange
    ) {
      context.withObject(at: .root(p)) { (o) in
        if o.value == .full(.initialized) { return }

        // If the parameter is `let` or `inout`, it's been (partially) consumed since it was
        // initialized in the entry context.
        if k == .set {
          diagnostics.insert(
            .uninitializedSetParameter(beforeReturningFrom: f, in: self, at: site))
        } else {
          diagnostics.insert(
            .illegalParameterEscape(consumedBy: o.value.consumers, in: self, at: site))
        }
      }
    }

    /// Checks that entry parameter `p` is deinitialized in `context`, inserting definitialization
    /// before instruction `i` if it isn't, reporting diagnostics at `site`.
    func ensureUninitializedOnExit(
      _ p: Operand, in context: inout Context,
      insertingDeinitializationBefore i: InstructionID,
      reportingDiagnosticsAt site: SourceRange
    ) {
      context.withObject(
        at: .root(p),
        { (o) in
          let s = o.value.initializedSubfields
          if s == [[]] && isDeinit(i.function) {
            // We cannot call `deinit` in `deinit` itself.
            insertDeinitParts(
              of: p, before: i,
              anchoringInstructionsTo: site, reportingDiagnosticsTo: &diagnostics)
          } else {
            insertDeinit(
              p, at: s, before: i,
              anchoringInstructionsTo: site, reportingDiagnosticsTo: &diagnostics)
          }

          o.value = .full(.uninitialized)
        })
    }

    /// Checks that the return value is initialized in `context`.
    func ensureReturnValueIsInitialized(
      in context: inout Context, at site: SourceRange
    ) {
      let p = returnValue(of: f)!
      let isInitialized = context.withObject(at: .root(p)) { (o) in
        o.value == .full(.initialized)
      }
      if !isInitialized {
        diagnostics.insert(.missingReturn(inFunctionReturning: self[f].output, at: site))
      }
    }

    /// Checks that the state of the projection of `sources` in the region defined at `start` and
    /// exited with `exit` is consistent with `access`, updating `context` accordingly.
    ///
    /// `start` is the definition of projection (e.g., the result of `project`) dominating `i`,
    /// which is a corresponding exit. `context.locals[start]` is the unique address of the object
    /// `o` being projected in that region. `sources` are the addresses of the objects notionally
    /// containing `o`.
    ///
    /// If `access` is `.let`, `.inout`, or `.set`, `o` must be fully initialized. If `access` is
    /// `sink`, `o` must be fully deinitialized. implicit deinitialization is inserted to maintain
    /// the latter requirement.
    func finalize(
      region start: Operand, projecting access: AccessEffect, from sources: Set<AbstractLocation>,
      exitedWith exit: InstructionID,
      in context: inout Context
    ) {
      // Skip the instruction if an error occurred upstream.
      guard let v = context.locals[start] else {
        assert(diagnostics.containsError)
        return
      }

      let l = v.unwrapLocations()!.uniqueElement!
      let projection = context.withObject(at: l, { $0 })

      switch access {
      case .let, .inout:
        assert(projection.value == .full(.initialized) || !projection.value.consumers.isEmpty)
        for c in projection.value.consumers {
          diagnostics.insert(.error(cannotConsume: access, at: self[c].site))
        }

      case .set:
        assert(projection.value == .full(.initialized) || !projection.value.consumers.isEmpty)
        for c in projection.value.consumers {
          diagnostics.insert(.error(cannotConsume: access, at: self[c].site))
        }
        for s in sources {
          context.withObject(at: s, { $0.value = .full(.initialized) })
        }

      case .sink:
        insertDeinit(
          start, at: projection.value.initializedSubfields, before: exit,
          anchoringInstructionsTo: self[exit].site, reportingDiagnosticsTo: &diagnostics)
        context.withObject(at: l, { $0.value = .full(.uninitialized) })

      case .yielded:
        unreachable()
      }

      context.memory[l] = nil
    }
  }

  /// Returns the initial context in which `f` should be interpreted.
  private func entryContext(of f: Function.ID) -> Context {
    let function = self[f]
    var result = Context()

    let entry = Block.ID(f, function.entry!)
    addParameter(.set, function.output, of: entry, at: function.inputs.count, in: &result)
    for i in function.inputs.indices {
      addParameter(function.inputs[i].type, of: entry, at: i, in: &result)
    }

    return result
  }

  /// Configure in `context` the initial state of the parameter at `position` in `entry`, which
  /// has type `t`.
  private func addParameter(
    _ t: ParameterType, of entry: Block.ID, at position: Int,
    in context: inout Context
  ) {
    addParameter(t.access, t.bareType, of: entry, at: position, in: &context)
  }

  /// Configure in `context` the initial state of the parameter at `position` in `entry`, which
  /// has type `t` passed with capability `k`.
  private func addParameter(
    _ k: AccessEffect, _ t: AnyType, of entry: Block.ID, at position: Int,
    in context: inout Context
  ) {
    let l = AbstractTypeLayout(of: t, definedIn: program)
    let p = Operand.parameter(entry, position)

    switch k {
    case .let, .inout, .sink:
      let a = AbstractLocation.root(p)
      context.locals[p] = .locations([a])
      context.memory[a] = .init(layout: l, value: .full(.initialized))

    case .set:
      let a = AbstractLocation.root(p)
      context.locals[p] = .locations([a])
      context.memory[a] = .init(layout: l, value: .full(.uninitialized))

    case .yielded:
      preconditionFailure("cannot represent instance of yielded type")
    }
  }

  /// Assigns a fully initialized object to the virtual register defined by `i` in `context`.
  private func initializeRegister(createdBy i: InstructionID, in context: inout Context) {
    if let t = self[i].result {
      context.locals[.register(i)] = .object(
        .init(layout: .init(of: t.ast, definedIn: program), value: .full(.initialized)))
    }
  }

  /// Assigns the virtual register defined by `i` to the location of the storage projected by `i`,
  /// using `t` to set the initial state of that storage.
  private func initializeRegister(
    createdBy i: InstructionID, projecting t: RemoteType, in context: inout Context
  ) {
    let l = AbstractLocation.root(.register(i))
    context.memory[l] = .init(
      layout: AbstractTypeLayout(of: t.bareType, definedIn: program),
      value: .full(t.access == .set ? .uninitialized : .initialized))
    context.locals[.register(i)] = .locations([l])
  }

  /// Inserts IR for the deinitialization of `root` at given `initializedSubfields` before
  /// instruction `i`, anchoring instructions to `site`.
  private mutating func insertDeinit(
    _ root: Operand, at initializedSubfields: [RecordPath], before i: InstructionID,
    anchoringInstructionsTo site: SourceRange,
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) {
    for path in initializedSubfields {
      Emitter.withInstance(insertingIn: &self, reportingDiagnosticsTo: &log) { (e) in
        e.insertionPoint = .before(i)
        let s = e.emitSubfieldView(root, at: path, at: site)
        e.emitDeinit(s, at: site)
      }
    }
  }

  /// Inserts ID for the deinitialization of `whole`'s parts before instruction `i`, anchoring
  /// new instructions to `site`.
  private mutating func insertDeinitParts(
    of whole: Operand, before i: InstructionID,
    anchoringInstructionsTo site: SourceRange,
    reportingDiagnosticsTo log: inout DiagnosticSet
  ) {
    Emitter.withInstance(insertingIn: &self, reportingDiagnosticsTo: &log) { (e) in
      e.insertionPoint = .before(i)
      e.emitDeinitParts(of: whole, at: site)
    }
  }

  /// Returns the site at which diagnostics related to the parameter `p` should be reported in `f`.
  private func diagnosticSite(for p: Parameter, in f: Function.ID) -> SourceRange {
    guard let d = p.decl else { return .empty(at: self[f].site.start) }
    switch d.kind {
    case ParameterDecl.self:
      return program.ast[ParameterDecl.ID(d)!].identifier.site
    default:
      return program.ast[d].site
    }
  }

}

/// An abstract interpretation context.
private typealias Context = AbstractContext<State>

extension Context {

  /// Returns `true` iff the object at `a` is fully initialized.
  fileprivate mutating func isStaticallyInitialized(_ a: Operand) -> Bool {
    if case .constant = a { unreachable("operand is a constant") }
    let locations = locals[a]!.unwrapLocations()!

    let v = withObject(at: locations.first!, \.value)
    assert(
      locations.allSatisfy({ (l) in withObject(at: l, { $0.value == v }) }),
      "bad context")

    switch v {
    case .full(.initialized):
      return true
    case .full(.uninitialized), .full(.consumed):
      return false
    default:
      UNIMPLEMENTED()
    }
  }

}

/// A map from function block to the context of the abstract interpreter before and after the
/// evaluation of its instructions.
private typealias Contexts = [Function.Blocks.Address: (before: Context, after: Context)]

/// The initialization state of an object or sub-object.
///
/// Instances form a lattice whose supremum is `.initialized` and infimum is `.consumed(by: s)`
/// where `s` is the set of all instructions. The meet of two elements denotes the conservative
/// superposition of two initialization states.
private enum State: AbstractDomain {

  /// A set of consumers.
  typealias Consumers = Set<InstructionID>

  /// Object is initialized.
  case initialized

  /// Object is uninitialized.
  case uninitialized

  /// Object was consumed the users in the payload.
  ///
  /// An object can be consumed by multiple users after merging after-contexts in which it's been
  /// consumed by different users.
  ///
  /// - Requires: The payload is not empty.
  case consumed(by: Consumers)

  /// Forms a new state by merging `lhs` with `rhs`.
  static func && (lhs: State, rhs: State) -> State {
    switch lhs {
    case .initialized:
      return rhs

    case .uninitialized:
      return rhs == .initialized ? lhs : rhs

    case .consumed(let a):
      if case .consumed(let b) = rhs {
        return .consumed(by: a.union(b))
      } else {
        return .consumed(by: a)
      }
    }
  }

}

extension State: CustomStringConvertible {

  var description: String {
    switch self {
    case .initialized:
      return "\u{23Fa}"
    case .uninitialized:
      return "\u{25cb}"
    case .consumed(let consumers):
      return "←\(consumers)"
    }
  }

}

/// Classification of a record type's subfields into uninitialized, initialized, and consumed sets.
private struct SubfieldsByInitializationState {

  /// The paths to the initialized parts.
  var initialized: [RecordPath]

  /// The paths to the uninitialized parts.
  var uninitialized: [RecordPath]

  /// The paths to the consumed parts, along with the users that consumed them.
  var consumed: [(subfield: RecordPath, consumers: State.Consumers)]

}

extension AbstractObject.Value where Domain == State {

  /// If `self` is `.partial`, the paths to `self`'s parts; otherwise, `nil`.
  fileprivate var subfields: SubfieldsByInitializationState? {
    if case .full = self { return nil }
    var paths = SubfieldsByInitializationState(initialized: [], uninitialized: [], consumed: [])
    gatherSubobjectPaths(prefixedBy: [], into: &paths)
    return paths
  }

  /// The initialized subfields.
  fileprivate var initializedSubfields: [RecordPath] {
    switch self {
    case .full(.initialized):
      return [[]]
    case .full(.uninitialized), .full(.consumed):
      return []
    case .partial:
      return subfields!.initialized
    }
  }

  /// If `self` is `.partial`, inserts the paths to its parts into `paths`, prefixing each inserted
  /// element by `prefix`.
  ///
  /// - Requires: `self` is canonical.
  private func gatherSubobjectPaths(
    prefixedBy prefix: RecordPath,
    into paths: inout SubfieldsByInitializationState
  ) {
    guard case .partial(let subobjects) = self else { return }

    for i in 0..<subobjects.count {
      switch subobjects[i] {
      case .full(.initialized):
        paths.initialized.append(prefix + [i])
      case .full(.uninitialized):
        paths.uninitialized.append(prefix + [i])
      case .full(.consumed(let c)):
        paths.consumed.append((subfield: prefix + [i], consumers: c))
      case .partial(let parts):
        for p in parts {
          p.gatherSubobjectPaths(prefixedBy: prefix + [i], into: &paths)
        }
      }
    }
  }

  /// The consumers of the object.
  fileprivate var consumers: State.Consumers {
    switch self {
    case .full(.initialized), .full(.uninitialized):
      return []
    case .full(.consumed(let c)):
      return c
    case .partial(let parts):
      return parts.reduce(into: [], { (s, p) in s.formUnion(p.consumers) })
    }
  }

  /// Reports a diagnostic to `log` at `site` if `self != .full(.initialized)`.
  fileprivate func checkInitialized(
    at site: SourceRange, reportingDiagnosticsTo log: inout DiagnosticSet
  ) {
    switch self {
    case .full(.initialized):
      return

    case .full(.uninitialized):
      log.insert(.useOfUninitializedObject(at: site))

    case .full(.consumed):
      log.insert(.useOfConsumedObject(at: site))

    case .partial:
      if subfields!.consumed.isEmpty {
        log.insert(.useOfPartiallyInitializedObject(at: site))
      } else {
        log.insert(.useOfPartiallyConsumedObject(at: site))
      }
    }
  }

  /// Returns `lhs` merged with `rhs`.
  fileprivate static func && (lhs: Self, rhs: Self) -> Self {
    switch (lhs.canonical, rhs.canonical) {
    case (.full(let lhs), .full(let rhs)):
      return .full(lhs && rhs)

    case (.partial(let lhs), .partial(let rhs)):
      assert(lhs.count == rhs.count)
      return .partial(zip(lhs, rhs).map(&&))

    case (.partial(let lhs), _):
      return .partial(lhs.map({ $0 && rhs }))

    case (_, .partial(let rhs)):
      return .partial(rhs.map({ lhs && $0 }))
    }
  }

  /// Returns the paths of the parts that are initialized in `l` and either uninitialized or
  /// consumed in `r`.
  ///
  /// - Requires: `l` and `r` are canonical and have the same layout
  static func - (l: Self, r: Self) -> [RecordPath] {
    switch (l, r) {
    case (_, .full(.initialized)):
      // No part of LHS is not initialized in RHS.
      return []

    case (let lhs, .full):
      // RHS is fully consumed or uninitialized.
      if let p = lhs.subfields {
        return p.initialized
      } else if lhs == .full(.initialized) {
        return [[]]
      } else {
        return []
      }

    case (.full(.initialized), let rhs):
      // RHS is partially initialized.
      let p = rhs.subfields!
      return p.uninitialized + p.consumed.map(\.subfield)

    case (.full, _):
      // LHS is fully consumed or uninitialized.
      return []

    case (.partial(let lhs), .partial(let rhs)):
      // LHS and RHS are partially initialized.
      assert(lhs.count == rhs.count)
      return (0..<lhs.count).reduce(into: []) { (result, i) in
        result.append(contentsOf: (lhs[i] - rhs[i]).map({ [i] + $0 }))
      }
    }
  }

}

extension Diagnostic {

  fileprivate static func illegalMove(at site: SourceRange) -> Diagnostic {
    .error("illegal move", at: site)
  }

  fileprivate static func illegalParameterEscape(
    consumedBy consumers: State.Consumers? = nil,
    in module: Module,
    at site: SourceRange
  ) -> Diagnostic {
    if let c = consumers {
      return .error(
        "parameter was consumed", at: site,
        notes: c.map({ Diagnostic.note("escape happens here", at: module[$0].site) }))
    } else {
      return .error("parameter was consumed", at: site)
    }
  }

  fileprivate static func uninitializedSetParameter(
    beforeReturningFrom f: Function.ID,
    in module: Module,
    at site: SourceRange
  ) -> Diagnostic {
    let e = module[f].isSubscript ? "subscript" : "function"
    return .error("set parameter not initialized before \(e) returns", at: site)
  }

  fileprivate static func error(
    cannotConsume k: AccessEffect, at site: SourceRange
  ) -> Diagnostic {
    .error("cannot consume '\(k)' projection", at: site)
  }

  fileprivate static func useOfConsumedObject(at site: SourceRange) -> Diagnostic {
    .error("use of consumed object", at: site)
  }

  fileprivate static func useOfPartiallyConsumedObject(at site: SourceRange) -> Diagnostic {
    .error("use of partially consumed object", at: site)
  }

  fileprivate static func useOfPartiallyInitializedObject(at site: SourceRange) -> Diagnostic {
    .error("use of partially initialized object", at: site)
  }

  fileprivate static func useOfUninitializedObject(at site: SourceRange) -> Diagnostic {
    .error("use of uninitialized object", at: site)
  }

  fileprivate static func missingReturn(
    inFunctionReturning expectedReturnType: AnyType,
    at site: SourceRange
  ) -> Diagnostic {
    .error("missing return in function expected to return '\(expectedReturnType)'", at: site)
  }

}
