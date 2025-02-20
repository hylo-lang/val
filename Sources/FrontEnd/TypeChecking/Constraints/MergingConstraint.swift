import Utils

/// A constraint `L :> (R1, ..., Rn)` specifying that `L` is the type of a conditional or match
/// expression whose branches have types `R1, ..., Rn`.
struct MergingConstraint: Constraint, Hashable {

  /// The type of the expression.
  private(set) var supertype: AnyType

  /// The types of the branches.
  private(set) var branches: [AnyType]

  let origin: ConstraintOrigin

  /// Creates an instance with the given properties.
  init(_ supertype: AnyType, _ branches: [AnyType], origin: ConstraintOrigin) {
    self.supertype = supertype
    self.branches = branches
    self.origin = origin
  }

  /// Inserts the type variables that occur free in `self` into `s`.
  func collectOpenVariables(in s: inout Set<TypeVariable>) {
    supertype.collectOpenVariables(in: &s)
    for b in branches {
      b.collectOpenVariables(in: &s)
    }
  }

  mutating func modifyTypes(_ transform: (AnyType) -> AnyType) {
    update(&supertype, with: transform)
    for i in 0..<branches.count {
      update(&branches[i], with: transform)
    }
  }

}

extension MergingConstraint: CustomStringConvertible {

  var description: String { "\(supertype) :> \(list: branches)" }

}
