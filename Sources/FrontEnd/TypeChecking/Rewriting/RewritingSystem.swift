import Utils

/// A set of rewriting rules describing some equational equivalences.
struct RewritingSystem<Term: RewritingTerm> {

  /// The identifier of a rule in a rewriting system.
  typealias RuleID = Int

  /// The rules in the system, including those that may have been simplified.
  private(set) var rules: [RewritingRule<Term>]

  /// A map from terms to the rule of which they are the left-hand side.
  private var termToRule: Trie<Term, RuleID>

  /// Creates an empty system.
  init() {
    self.rules = []
    self.termToRule = Trie()
  }

  /// Rewrites `u` with the rules in `self` until a normal form is reached.
  ///
  /// The rewriting process is notionally nondeterministic unless `self` is confluent.
  func reduce(_ u: Term) -> Term {
    for p in u.indices {
      let (n, q) = termToRule.longestPrefix(startingWith: u[p...])
      if p != q, let r = n[[]] {
        let x = Term(u[..<p])
        let v = rules[r].rhs
        let z = u[(p + rules[r].lhs.count)...]
        return reduce(x + v + z)
      }
    }
    return u
  }

  /// Inserts the given rule using `compareOrder` to order pairs of terms.
  ///
  /// A rule *u => v* is notionally contained in a rewriting system if that system contains a set
  /// of rules capable of rewriting *u* to *v*. This set may not contain *u => v* itself.
  ///
  /// The return value is `(true, new)` if `r` is not already notionally contained in the system,
  /// where `new` is the identifier of a newly inserted rule that is encoding `r`. Otherwise, the
  /// return value is `(false, old)` where `old` is the identifier of a rule encoding `r`.
  ///
  /// - Precondition: The source of the rule is ordered after its target.
  @discardableResult
  mutating func insert(
    _ r: RewritingRule<Term>,
    orderingTermsWith compareOrder: (Term, Term) -> StrictOrdering
  ) -> (inserted: Bool, ruleAfterInsertion: RuleID) {
    precondition(compareOrder(r.lhs, r.rhs) == .descending, "invalid rewriting rule")
    precondition(!r.isSimplified)

    // If the source of the rule isn't associated with any other rule yet, inserts the rule and
    // return `(true, i)` where `i` is the position of the rule in `rules`. Otherwise, return
    // `(false, j)` where `j` is the position of a rule sharing the same source.
    let result = modify(&termToRule[r.lhs]) { (q) in
      if let old = q {
        return (inserted: false, ruleAfterInsertion: old)
      } else {
        q = rules.count
        rules.append(r)
        return (inserted: true, ruleAfterInsertion: q!)
      }
    }

    // Nothing more to do if the rule was inserted.
    if result.inserted {
      return result
    }

    // Otherwise, update the system to notionally contain the rule.
    let old = result.ruleAfterInsertion
    switch compareOrder(r.rhs, rules[old].rhs) {
    case .equal:
      return result

    case .descending:
      return insert(.init(r.rhs, rules[old].rhs), orderingTermsWith: compareOrder)

    case .ascending:
      // Let the u1 => v1 and u2 => v2 be the old and new rules, respectively. Remove u1 => v1 from
      // the system and add v1 => v2.
      rules[old].raiseFlags(.isRightSimplified)
      insert(.init(rules[old].rhs, r.rhs), orderingTermsWith: compareOrder)

      // Add u2 => v2.
      let q = rules.count
      termToRule[r.lhs] = q
      rules.append(r)
      return (inserted: true, ruleAfterInsertion: q)
    }
  }

  /// Turns `self` into a terminating and confluent rewriting system, using `compareOrder` to order
  /// pairs of terms.
  ///
  /// This method uses Knuth-Bendix completion algorithm to transform `self` into a terminating
  /// confluent system. The completion procedure is semi-decidable: it returns `true` if it
  /// succeeds or `false` if it suspects that it won't terminate.
  mutating func complete(orderingTermsWith compareOrder: (Term, Term) -> StrictOrdering) -> Bool {
    var visitedOverlaps = Set<OverlapIdentifier>()
    var pairs: [CriticalPair] = []
    var changed = true
    var insertions = 0

    while changed {
      changed = false

      forEachOverlap { (i, j, k) in
        if visitedOverlaps.insert(.init(i, j, at: k)).inserted {
          pairs.append(formCriticalPair(i, j, overlappingAt: k))
        }
      }

      while let p = pairs.popLast() {
        if let q = resolveCriticalPair(p, orderingTermsWith: compareOrder) {
          if insert(q, orderingTermsWith: compareOrder).inserted {
            changed = true
            insertions += 1
            if insertions > 100 { return false }
          }
        }
      }
    }

    leftSimplify()
    return true
  }

  /// Calls `action` on each overlap between two rules of the system.
  private func forEachOverlap(do action: (RuleID, RuleID, Term.Index) -> Void) {
    for i in rules.indices where !rules[i].isSimplified {
      forEachOverlap(involving: i, do: { (j, p) in action(i, j, p) })
    }
  }

  /// Calls `action` on each overlap involving `i`.
  private func forEachOverlap(involving i: RuleID, do action: (RuleID, Term.Index) -> Void) {
    let u = rules[i].lhs
    for p in u.indices {
      forEachOverlap(of: u[p...], in: termToRule[prefix: []]!) { (j) in
        // Ignore the overlap of a rule with itself at position 0.
        if (i == j) && (p == u.startIndex) { return }
        action(j, p)
      }
    }
  }

  /// Calls `action` on each identifier in `terms` denoting a rule having an overlap between its
  /// left-hand side and `suffix`.
  ///
  /// If the key/value pair `(t, i)` is contained in `terms`, then `t` is the suffix of some term
  /// `l` and `i` identifies a rewriting rule `l => r`.
  private func forEachOverlap(
    of suffix: Term.SubSequence, in terms: SubTrie<Term, RuleID>,
    do action: (RuleID) -> Void
  ) {
    var t = suffix
    var n = terms

    while let (head, tail) = t.headAndTail {
      if let m = n[prefix: [head]] {
        if let i = m[[]] { action(i) }
        t = tail
        n = m
      } else {
        return
      }
    }

    for e in n.elements {
      action(e.value)
    }
  }

  /// Returns the critical pair formed by the rules `lhs` and `rhs`, which overlap at the `i`-th
  /// position of `lhs`'s source.
  private func formCriticalPair(
    _ lhs: RuleID, _ rhs: RuleID, overlappingAt i: Int
  ) -> CriticalPair {
    // Let `lhs` and `rhs` denote rewriting rules u1 => v1 and u2 => v2, respectively.
    let (u1, v1) = rules[lhs].deconstructed
    let (u2, v2) = rules[rhs].deconstructed

    // If i + |u2| ≤ |u1|, then u1 = x·u2·z for some x and z.
    if i + u2.count <= u1.count {
      let x = u1[..<i]
      let z = u1[(i + u2.count)...]
      return CriticalPair(v1, x + v2 + z)
    }

    // Otherwise, u1 = xy and u2 = yz for some x, y, and z.
    else {
      let x = u1[..<i]
      let z = u2[(u1.count - i)...]
      return CriticalPair(v1 + z, x + v2)
    }
  }

  /// Adds a rule rewritng `p`'s first element to its second, or vice versa, using `compareOrder`
  /// to order pairs of terms.
  private func resolveCriticalPair(
    _ p: CriticalPair,
    orderingTermsWith compareOrder: (Term, Term) -> StrictOrdering
  ) -> RewritingRule<Term>? {
    // Fast path: critical pair is trivial without any reduction.
    if p.first == p.second { return nil }

    // Reduce both sides of the pair.
    let b1 = reduce(p.first)
    let b2 = reduce(p.second)

    // There are only three cases to consider because we assume a total order on the terms. That is
    // unlike traditional implementations of Knuth-Bendix, which must fail on incomparable terms.
    switch compareOrder(b1, b2) {
    case .equal:
      // b1 = b2: the pair is trivial and there's nothing more to do.
      return nil

    case .ascending:
      // b1 < b2: create a new rule b2 => b1.
      return .init(b2, b1)

    case .descending:
      // b2 < b1: create a new rule b1 => b2.
      return .init(b1, b2)
    }
  }

  /// Removes the rules in `self` whose left hand side can be reduced by a simpler rule.
  private mutating func leftSimplify() {
    for i in 0..<rules.count where !rules[i].isSimplified {
      for p in rules[i].lhs.indices {
        if simplify(i, lookingForTermsInSuffixFrom: p) { break }
      }
    }
  }

  /// Removes `i` from `self` if the suffix of its left-hand side starting from `p` contains a
  /// subterm that can be reduced by another rule.
  private mutating func simplify(_ i: RuleID, lookingForTermsInSuffixFrom p: Term.Index) -> Bool {
    let w = rules[i].lhs
    var n = termToRule[prefix: []]!

    for q in w[p...].indices {
      if let m = n[prefix: w[q..<w.index(after: q)]] {
        if let j = m[[]], i != j {
          rules[i].raiseFlags(.isLeftSimplified)
          termToRule[rules[i].lhs] = nil
          return true
        } else {
          n = m
        }
      } else {
        return false
      }
    }

    return false
  }

  /// The rewritings of a term by two different rules or the same rule at two different positions.
  private struct CriticalPair {

    /// The first term of the pair.
    let first: Term

    /// The first term of the pair.
    let second: Term

    /// Creates an instance with the given terms.
    init(_ u: Term, _ v: Term) {
      self.first = u
      self.second = v
    }

  }

  /// The identifier of an overlap between rewriting rules.
  private struct OverlapIdentifier: Hashable {

    /// The raw value of this identifier.
    private let rawValue: UInt64

    /// Creates an instance identifying an overlap between `lhs` and `rhs` at the `i`-th position
    /// of `lhs`'s source.
    init(
      _ lhs: RewritingSystem.RuleID, _ rhs: RewritingSystem.RuleID,
      at i: Term.Index
    ) {
      precondition((i | lhs | rhs) & ~((1 << 16) - 1) == 0)
      self.rawValue = UInt64(truncatingIfNeeded: i | (lhs << 16) | (rhs << 32))
    }

  }

}
