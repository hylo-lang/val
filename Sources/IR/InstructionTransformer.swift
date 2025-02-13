import FrontEnd
import Utils

/// A type that transforms the parts of IR instructions.
protocol InstructionTransformer {

  /// Returns a transformed copy of `t` for use in `ir`.
  func transform(_ t: AnyType, in ir: inout IR.Program) -> AnyType

  /// Returns a transformed copy of `o` for use in `ir`.
  func transform(_ o: Operand, in ir: inout IR.Program) -> Operand

  /// Returns a transformed copy of `b` for use in `ir`.
  func transform(_ b: Block.ID, in ir: inout IR.Program) -> Block.ID

}

extension InstructionTransformer {

  /// Returns a transformed copy of `t` for use in `ir`.
  func transform(_ t: IR.`Type`, in ir: inout IR.Program) -> IR.`Type` {
    .init(ast: transform(t.ast, in: &ir), isAddress: t.isAddress)
  }

  /// Returns a transformed copy of the elements in `s` for use in `ir`.
  func transform<S: Sequence<Operand>>(_ s: S, in ir: inout IR.Program) -> [Operand] {
    s.map({ (a) in transform(a, in: &ir) })
  }

}

extension IR.Program {

  /// Inserts a copy of `i`, which is in `m`, at `p`, which is in `n`, transforming its parts with
  /// `t` and returning its identifier.
  mutating func rewrite<T: InstructionTransformer>(
    _ i: InstructionID, from m: Module.ID, transformedBy t: inout T,
    at p: InsertionPoint, in n: Module.ID
  ) -> InstructionID {
    switch modules[m]![i] {
    case let s as Access:
      let x0 = t.transform(s.source, in: &self)
      return insert(at: p, in: n) { (target) in
        Access(s.capabilities, from: x0, at: s.site, in: target)
      }

    case let s as AddressToPointer:
      let x0 = t.transform(s.source, in: &self)
      return insert(at: p, in: n) { (target) in
        AddressToPointer(x0, at: s.site, in: target)
      }

    case let s as AdvancedByBytes:
      let x0 = t.transform(s.base, in: &self)
      let x1 = t.transform(s.byteOffset, in: &self)
      return insert(at: p, in: n) { (target) in
        AdvancedByBytes(source: x0, offset: x1, at: s.site, in: target)
      }

    case let s as AdvancedByStrides:
      let x0 = t.transform(s.base, in: &self)
      return insert(at: p, in: n) { (target) in
        AdvancedByStrides(x0, offset: s.offset, at: s.site, in: target)
      }

    case let s as AllocStack:
      let x0 = t.transform(s.allocatedType, in: &self)
      return insert(at: p, in: n) { (target) in
        AllocStack(x0, at: s.site, in: target)
      }

    case let s as Branch:
      let x0 = t.transform(s.target, in: &self)
      return insert(at: p, in: n) { (target) in
        Branch(to: x0, at: s.site, in: target)
      }

    case let s as Call:
      let x0 = t.transform(s.callee, in: &self)
      let x1 = t.transform(s.arguments, in: &self)
      let x2 = t.transform(s.output, in: &self)
      return insert(at: p, in: n) { (target) in
        Call(applying: x0, to: x1, writingResultTo: x2, at: s.site, in: target)
      }

    case let s as CallFFI:
      let x0 = t.transform(s.returnType, in: &self)
      let x1 = t.transform(s.operands, in: &self)
      return insert(at: p, in: n) { (target) in
        CallFFI(returning: x0, applying: s.callee, to: x1, at: s.site, in: target)
      }

    case let s as CaptureIn:
      let x0 = t.transform(s.source, in: &self)
      let x1 = t.transform(s.target, in: &self)
      return insert(at: p, in: n) { (target) in
        CaptureIn(x0, in: x1, at: s.site, in: target)
      }

    case let s as CloseCapture:
      let x0 = t.transform(s.start, in: &self)
      return insert(at: p, in: n) { (target) in
        CloseCapture(x0, at: s.site, in: target)
      }

    case let s as CloseUnion:
      let x0 = t.transform(s.start, in: &self)
      return insert(at: p, in: n) { (target) in
        CloseUnion(x0, at: s.site, in: target)
      }

    case let s as CondBranch:
      let x0 = t.transform(s.condition, in: &self)
      let x1 = t.transform(s.targetIfTrue, in: &self)
      let x2 = t.transform(s.targetIfFalse, in: &self)
      return insert(at: p, in: n) { (target) in
        CondBranch(if: x0, then: x1, else: x2, at: s.site, in: target)
      }

    case let s as ConstantString:
      return modules[n]!.insert(s, at: p)

    case let s as DeallocStack:
      let x0 = t.transform(s.location, in: &self)
      return insert(at: p, in: n) { (target) in
        DeallocStack(for: x0, at: s.site, in: target)
      }

    case let s as EndAccess:
      let x0 = t.transform(s.start, in: &self)
      return insert(at: p, in: n) { (target) in
        EndAccess(x0, at: s.site, in: target)
      }

    case let s as EndProject:
      let x0 = t.transform(s.start, in: &self)
      return insert(at: p, in: n) { (target) in
        EndProject(x0, at: s.site, in: target)
      }

    case let s as GenericParameter:
      return modules[n]!.insert(s, at: p)

    case let s as GlobalAddr:
      return modules[n]!.insert(s, at: p)

    case let s as CallBuiltinFunction:
      let x0 = t.transform(s.operands, in: &self)
      return insert(at: p, in: n) { (target) in
        CallBuiltinFunction(applying: s.callee, to: x0, at: s.site, in: target)
      }

    case let s as MarkState:
      let x0 = t.transform(s.storage, in: &self)
      return insert(at: p, in: n) { (target) in
        MarkState(x0, initialized: s.initialized, at: s.site, in: target)
      }

    case let s as MemoryCopy:
      let x0 = t.transform(s.source, in: &self)
      let x1 = t.transform(s.target, in: &self)
      return insert(at: p, in: n) { (target) in
        MemoryCopy(x0, x1, at: s.site, in: target)
      }

    case let s as Load:
      let x0 = t.transform(s.source, in: &self)
      return insert(at: p, in: n) { (target) in
        Load(x0, at: s.site, in: target)
      }

    case let s as OpenCapture:
      let x0 = t.transform(s.source, in: &self)
      return insert(at: p, in: n) { (target) in
        OpenCapture(x0, at: s.site, in: target)
      }

    case let s as OpenUnion:
      let x0 = t.transform(s.container, in: &self)
      let x1 = t.transform(s.payloadType, in: &self)
      return insert(at: p, in: n) { (target) in
        OpenUnion(x0, as: x1, forInitialization: s.isUsedForInitialization, at: s.site, in: target)
      }

    case let s as PointerToAddress:
      let x0 = t.transform(s.source, in: &self)
      let x1 = RemoteType(t.transform(^s.target, in: &self))!
      return insert(at: p, in: n) { (target) in
        PointerToAddress(x0, to: x1, at: s.site, in: target)
      }

    case let s as Project:
      let r = FunctionReference(
        to: s.callee, in: modules[m]!,
        specializedBy: s.specialization, in: modules[m]!.scope(containing: i))
      let oldCallee = Operand.constant(r)
      let newCallee = t.transform(oldCallee, in: &self).constant as! FunctionReference

      let x0 = RemoteType(t.transform(^s.projection, in: &self))!
      let x1 = t.transform(s.operands, in: &self)
      return insert(at: p, in: n) { (target) in
        Project(
          x0, applying: newCallee.function, specializedBy: newCallee.specialization, to: x1,
          at: s.site, in: target)
      }

    case let s as ReleaseCaptures:
      let x0 = t.transform(s.container, in: &self)
      return insert(at: p, in: n) { (target) in
        ReleaseCaptures(x0, at: s.site, in: target)
      }

    case let s as Return:
      return modules[n]!.insert(s, at: p)

    case let s as Store:
      let x0 = t.transform(s.object, in: &self)
      let x1 = t.transform(s.target, in: &self)
      return insert(at: p, in: n) { (target) in
        Store(x0, at: x1, at: s.site, in: target)
      }

    case let s as SubfieldView:
      let x0 = t.transform(s.recordAddress, in: &self)
      return insert(at: p, in: n) { (target) in
        SubfieldView(of: x0, subfield: s.subfield, at: s.site, in: target)
      }

    case let s as Switch:
      let x0 = t.transform(s.index, in: &self)
      let x1 = s.successors.map({ (b) in t.transform(b, in: &self) })
      return insert(at: p, in: n) { (target) in
        Switch(on: x0, toOneOf: x1, at: s.site, in: target)
      }

    case let s as UnionDiscriminator:
      let x0 = t.transform(s.container, in: &self)
      return insert(at: p, in: n) { (target) in
        UnionDiscriminator(x0, at: s.site, in: target)
      }

    case let s as UnionSwitch:
      let x0 = t.transform(s.discriminator, in: &self)
      let x1 = UnionType(t.transform(^s.union, in: &self))!
      let x2 = s.targets.reduce(into: UnionSwitch.Targets()) { (d, kv) in
        _ = d[t.transform(kv.key, in: &self)].setIfNil(t.transform(kv.value, in: &self))
      }
      return insert(at: p, in: n) { (target) in
        UnionSwitch(over: x0, of: x1, toOneOf: x2, at: s.site, in: target)
      }

    case let s as Unreachable:
      return modules[n]!.insert(s, at: p)

    case let s as Yield:
      let x0 = t.transform(s.projection, in: &self)
      return insert(at: p, in: n) { (target) in
        Yield(s.capability, x0, at: s.site, in: target)
      }

    default:
      unreachable()
    }
  }

  /// Inserts the result of `makeInstruction` at `p`, which is in `m`.
  private mutating func insert<T: Instruction>(
    at p: InsertionPoint, in m: Module.ID, _ makeInstruction: (inout Module) -> T
  ) -> InstructionID {
    modify(&modules[m]!) { (x) in
      let s = makeInstruction(&x)
      return x.insert(s, at: p)
    }
  }

}
