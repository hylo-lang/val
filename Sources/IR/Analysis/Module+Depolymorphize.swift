import FrontEnd
import OrderedCollections
import Utils

extension IR.Program {

  /// Generates the non-parametric reslient APIs of the modules in `self`.
  public mutating func depolymorphize(profileWith profiler: ProfilingMeasurements? = nil) {
    let probe = profiler?.createAndStartProfilingProbe(MeasurementType.Depolymorphize)
    defer { probe?.stop() }
    for m in modules.keys {
      depolymorphize(m)
    }
  }

  /// Generates the non-parametric resilient API of `m`.
  public mutating func depolymorphize(_ m: Module.ID) {
    for k in modules[m]!.functions.keys {
      let f = modules[m]!.functions[k]!

      // Ignore declarations without definition.
      if f.entry == nil { continue }

      // All non-generic functions are deploymorphized.
      if !f.isGeneric {
        depolymorphize(k, definedIn: m)
        continue
      }

      // Public generic functions are existentialized.
      if f.linkage == .external {
        _ = existentialize(k)
      }
    }
  }

  /// Replaces uses of parametric types and functions in `f` with their monomorphic or existential
  /// counterparts.
  private mutating func depolymorphize(_ f: Function.ID, definedIn m: Module.ID) {
    for b in modules[m]!.blocks(in: f) {
      for i in modules[m]!.instructions(in: b) {
        switch modules[m]![i] {
        case is Call:
          depolymorphize(call: i, definedIn: m)
        case is Project:
          depolymorphize(project: i, definedIn: m)
        default:
          continue
        }
      }
    }
  }

  /// Iff `i` is a call to a generic function, replaces it by an instruction applying a
  /// depolymorphized version of its callee.
  ///
  /// - Requires: `i` identifies a `CallInstruction`
  private mutating func depolymorphize(call i: InstructionID, definedIn m: Module.ID) {
    let s = modules[m]![i] as! Call
    guard
      let callee = s.callee.constant as? FunctionReference,
      !callee.specialization.isEmpty
    else { return }

    // TODO: Use existentialization unless the function is inlinable

    let g = monomorphize(callee, usedIn: modules[m]!.scope(containing: i))
    let r = FunctionReference(to: g, in: modules[m]!)
    let new = modules[m]!.makeCall(
      applying: .constant(r), to: Array(s.arguments), writingResultTo: s.output, at: s.site)
    modules[m]!.replace(i, with: new)
  }

  /// Iff `i` is the projection through a generic subscript, replaces it by an instruction applying
  /// a depolymorphized version of its callee.
  ///
  /// - Requires: `i` identifies a `ProjectInstruction`
  private mutating func depolymorphize(project i: InstructionID, definedIn m: Module.ID) {
    let s = modules[m]![i] as! Project
    guard !s.specialization.isEmpty else { return }

    // TODO: Use existentialization unless the subscript is inlinable

    let z = base.canonical(s.specialization, in: modules[m]!.scope(containing: i))
    let g = monomorphize(s.callee, for: z, usedIn: modules[m]!.scope(containing: i))
    let new = modules[m]!.makeProject(
      s.projection, applying: g, specializedBy: .empty, to: s.operands, at: s.site)
    modules[m]!.replace(i, with: new)
  }

  /// Returns a depolymorphized copy of `base` in which parametric parameters have been notionally
  /// replaced by parameters accepting existentials.
  ///
  /// The returned function takes `n` additional parameters where `n` is the length of `arguments`.
  /// For example, assume `base` is defined as the generic function below, which takes two generic
  /// parameters:
  ///
  ///      fun foo<T: P, s: Int>(a: T, b: T[s]) -> T
  ///
  /// Its existentialized form is a function:
  ///
  ///      fun foo_e(a: RawPointer, b, RawPointer, T: WitnessTable, s: Int) -> RawPointer
  ///
  /// The pair `(a, T)` is a notional existential container representing the first argument of the
  /// parametric function. The triple `(a, T, s)` represents the second argument.
  private mutating func existentialize(_ base: Function.ID) -> Function.ID {
    // TODO: Implement me
    return base
  }

  /// Returns the monomorphized form of `r` for use in `scopeOfUse`, reading definitions from `ir`.
  private mutating func monomorphize(
    _ r: FunctionReference, usedIn scopeOfUse: AnyScopeID
  ) -> Function.ID {
    monomorphize(r.function, for: r.specialization, usedIn: scopeOfUse)
  }

  /// Returns a reference to the monomorphized form of `f` for specialization `z` in `scopeOfUse`,
  /// reading definitions from `ir`.
  fileprivate mutating func monomorphize(
    _ f: Function.ID, for z: GenericArguments, usedIn scopeOfUse: AnyScopeID
  ) -> Function.ID {
    precondition(z.allSatisfy(\.value.isCanonical))
    let result = demandMonomorphizedDeclaration(of: f, for: z, usedIn: scopeOfUse)

    let target = base.module(containing: scopeOfUse)
    if modules[target]![result].entry != nil {
      return result
    }

    let source = module(defining: f)
    var rewrittenBlock: [Block.ID: Block.ID] = [:]
    for b in modules[source]![f].blocks.addresses {
      let s = Block.ID(f, b)
      let inputs = modules[source]![s].inputs.map { (t) in
        monomorphize(t, for: z, usedIn: scopeOfUse)
      }
      let t = modules[target]![result].appendBlock(in: modules[source]![s].scope, taking: inputs)
      rewrittenBlock[s] = Block.ID(result, t)
    }

    let rewrittenGenericValue = modules[target]!.defineGenericValueArguments(z, in: result)
    var monomorphizer = Monomorphizer(
      specialization: z, scopeOfUse: scopeOfUse,
      rewrittenGenericValue: rewrittenGenericValue, rewrittenBlock: rewrittenBlock)

    // Iterate over the basic blocks of the source function in a way that guarantees we always
    // visit definitions before their uses.
    let cfg = modules[source]![f].cfg()
    let sourceBlocks = DominatorTree(function: f, cfg: cfg, in: modules[source]!).bfs
    for b in sourceBlocks {
      let s = Block.ID(f, b)
      let t = rewrittenBlock[s]!

      for a in modules[source]![s].instructions.addresses {
        let i = InstructionID(s, a)
        switch modules[source]![i] {
        case is GenericParameter:
          rewrite(genericParameter: i, to: t)
        case is Return:
          rewrite(return: i, to: t)
        default:
          rewrite(i, to: t)
        }
      }
    }

    return result

    /// Rewrites `i`, which is in `source`, at the end of `b`, which is in `target`.
    func rewrite(_ i: InstructionID, to b: Block.ID) {
      let j = self.rewrite(
        i, from: source, transformedBy: &monomorphizer,
        at: .end(of: b), in: target)
      monomorphizer.rewrittenInstruction[i] = j
    }

    /// Rewrites `i`, which is in `source`, at the end of `b`, which is in `target`.
    func rewrite(genericParameter i: InstructionID, to b: Block.ID) {
      let s = modules[source]![i] as! GenericParameter
      monomorphizer.rewrittenInstruction[i] = monomorphizer.rewrittenGenericValue[s.parameter]!
    }

    /// Rewrites `i`, which is in `source`, at the end of `b`, which is in `target`.
    func rewrite(return i: InstructionID, to b: Block.ID) {
      let s = modules[source]![i] as! Return
      let j = modify(&modules[target]!) { (m) in
        for i in rewrittenGenericValue.values.reversed() {
          m.append(m.makeDeallocStack(for: .register(i), at: s.site), to: b)
        }
        return m.append(m.makeReturn(at: s.site), to: b)
      }
      monomorphizer.rewrittenInstruction[i] = j
    }
  }

  /// Returns a reference to the monomorphized form of requirement `r` for `specialization` in
  /// `scopeOfUse`, reading definitions from `ir`.
  fileprivate mutating func monomorphize(
    _ r: AnyDeclID, requiredBy trait: TraitType,
    for specialization: GenericArguments, usedIn scopeOfUse: AnyScopeID
  ) -> Function.ID {
    let receiver = base[trait.decl].receiver.id
    let model = specialization[receiver]!.asType!

    guard let c = base.conformance(of: model, to: trait, exposedTo: scopeOfUse) else {
      fatalError("expected '\(model)' to conform to '\(trait)'")
    }

    let s = base.module(containing: scopeOfUse)
    let i = c.implementations[r]!
    let d = modules[s]!.demandDeclaration(lowering: i)

    // Nothing to do if the implementation isn't generic.
    if modules[s]![d].genericParameters.isEmpty {
      return d
    }

    // Otherwise, the generic arguments of the implementation are supplied by the conformance,
    // except for the argument to the receiver parameter. This parameter may be associated with
    // a trait other the one declaring the requirement if the implementation is in an extension.
    var monomorphizationArguments = c.arguments
    if case .explicit(let d) = i, let t = base.traitDeclaring(d), t != trait {
      monomorphizationArguments[base[t.decl].receiver] = .type(model)
    } else {
      monomorphizationArguments[receiver] = .type(model)
    }

    return monomorphize(d, for: monomorphizationArguments, usedIn: scopeOfUse)
  }

  /// Returns the canonical form of `t`, specialized for specialization `z` in `scopeOfUse`.
  fileprivate func monomorphize(
    _ t: AnyType, for z: GenericArguments, usedIn scopeOfUse: AnyScopeID
  ) -> AnyType {
    let u = base.specialize(t, for: z, in: scopeOfUse)
    return base.canonical(u, in: scopeOfUse)
  }

  /// Returns `generic` specialized for specialization `z` in `scopeOfUse`.
  private func monomorphize(
    _ t: IR.`Type`, for z: GenericArguments, usedIn scopeOfUse: AnyScopeID
  ) -> IR.`Type` {
    let u = monomorphize(t.ast, for: z, usedIn: scopeOfUse)
    return .init(ast: u, isAddress: t.isAddress)
  }

  /// Returns the IR function monomorphizing `f` for specialization `z` in `scopeOfUse`.
  private mutating func demandMonomorphizedDeclaration(
    of f: Function.ID, for z: GenericArguments, usedIn scopeOfUse: AnyScopeID
  ) -> Function.ID {
    let source = modules[module(defining: f)]![f]
    let target = base.module(containing: scopeOfUse)

    precondition(!source.genericParameters.isEmpty, "function is not generic")
    precondition(
      source.genericParameters.allSatisfy({ z[$0] != nil }),
      "incomplete monomorphization arguments")

    let result = Function.ID(monomorphized: f, for: z)
    if modules[target]!.functions[result] != nil {
      return result
    }

    let inputs = source.inputs.map { (p) in
      let t = monomorphize(p.type.bareType, for: z, usedIn: scopeOfUse)
      return Parameter(decl: p.decl, type: ParameterType(p.type.access, t))
    }
    let output = monomorphize(source.output, for: z, usedIn: scopeOfUse)
    let entity = Function(
      isSubscript: source.isSubscript,
      site: source.site,
      linkage: .module,
      genericParameters: [],
      inputs: inputs,
      output: output,
      blocks: [])
    modules[target]!.addFunction(entity, for: result)
    return result
  }

}

extension Module {

  /// Allocates and initializes storage for each generic value argument in `specialization` in the
  /// entry of `monomorphized`, returning a map from a generic value parameter to its corresponding
  /// allocation that preserves the order of `specialization`.
  fileprivate mutating func defineGenericValueArguments(
    _ specialization: GenericArguments,
    in monomorphized: Function.ID
  ) -> OrderedDictionary<GenericParameterDecl.ID, InstructionID> {
    let insertionSite = SourceRange.empty(at: self[monomorphized].site.start)
    let entry = Block.ID(monomorphized, self[monomorphized].entry!)

    var genericValues = OrderedDictionary<GenericParameterDecl.ID, InstructionID>()

    for (k, v) in specialization {
      if v.asType != nil { continue }

      guard let w = v.asCompilerKnown(Int.self) else {
        UNIMPLEMENTED("arbitrary compile-time values")
      }

      let s = append(makeAllocStack(^program.ast.coreType("Int")!, at: insertionSite), to: entry)

      var log = DiagnosticSet()
      Emitter.withInstance(insertingIn: &self, reportingDiagnosticsTo: &log) { (e) in
        e.insertionPoint = .end(of: entry)
        e.emitStore(int: w, to: .register(s), at: insertionSite)
      }
      assert(log.isEmpty)

      genericValues[k] = s
    }

    return genericValues
  }

}

/// The monomorphization of a function.
private struct Monomorphizer: InstructionTransformer {

  /// The arguments for which instructions are monomorphized.
  let specialization: GenericArguments

  /// The scope in which instructions are monomorphized.
  let scopeOfUse: AnyScopeID

  /// A table from generic value parameter to the allocation of the storage containing its value.
  ///
  /// Generic value parameters are rewritten as local variables initialized at the beginning of
  /// the monomorphized function. Generic value arguments don't require deinitialization. Their
  /// local storage is deallocated before each rewritten return instruction.
  let rewrittenGenericValue: OrderedDictionary<GenericParameterDecl.ID, InstructionID>

  /// A map from basic block in `source` to its corresponding block in `result`.
  let rewrittenBlock: [Block.ID: Block.ID]

  /// A map from instruction in `source` to its corresponding instruction in `result`.
  var rewrittenInstruction: [InstructionID: InstructionID] = [:]

  /// Returns the canonical, monomorphized form of `t`.
  func transform(_ t: AnyType, in ir: inout IR.Program) -> AnyType {
    ir.monomorphize(^t, for: specialization, usedIn: scopeOfUse)
  }

  /// Returns a monomorphized copy of `o`.
  func transform(_ o: Operand, in ir: inout IR.Program) -> Operand {
    switch o {
    case .constant(let c):
      return .constant(transform(c, in: &ir))
    case .parameter(let b, let i):
      return .parameter(rewrittenBlock[b]!, i)
    case .register(let s):
      return .register(rewrittenInstruction[s]!)
    }
  }

  /// Returns a monomorphized copy of `b`.
  func transform(_ b: Block.ID, in ir: inout IR.Program) -> Block.ID {
    rewrittenBlock[b]!
  }

  /// Returns a monomorphized copy of `c`.
  private func transform(_ c: any Constant, in ir: inout IR.Program) -> any Constant {
    switch c {
    case let r as FunctionReference:
      return transform(r, in: &ir)
    case let t as MetatypeType:
      return MetatypeType(transform(^t, in: &ir))!
    default:
      return c
    }
  }

  /// Returns a monomorphized copy of `c`.
  private func transform(_ c: FunctionReference, in ir: inout IR.Program) -> FunctionReference {
    // Unspecialized references cannot refer to trait members, which are specialized for the
    // implicit `Self` parameter.
    if c.specialization.isEmpty {
      return c
    }

    let s = ir.base.module(containing: scopeOfUse)
    let f = transform(c.function, specializedBy: c.specialization, in: &ir)
    return FunctionReference(to: f, in: ir.modules[s]!)
  }

  /// Returns a monomorphized copy of `f` specialized by `z` for use in `scopeOfUse`.
  ///
  /// If `f` is a trait requirement, the result is a monomorphized version of that requirement's
  /// implementation, using `a` to identify the requirement's receiver. Otherwise, the result is
  /// a monomorphized copy of `f`.
  private func transform(
    _ f: Function.ID, specializedBy z: GenericArguments, in ir: inout IR.Program
  ) -> Function.ID {
    let p = ir.base.specialize(z, for: specialization, in: scopeOfUse)
    let q = ir.base.canonical(p, in: scopeOfUse)
    if let m = ir.base.requirementDeclaring(memberReferredBy: f) {
      return ir.monomorphize(m.decl, requiredBy: m.trait, for: q, usedIn: scopeOfUse)
    } else {
      return ir.monomorphize(f, for: q, usedIn: scopeOfUse)
    }
  }

}
