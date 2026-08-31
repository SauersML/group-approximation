---
rg: 2
id: stw99-problem-xiii-ssa-uct
kind: claim
title: Strongly self-absorbing algebras satisfy the UCT and are the known list (STW Problem XIII, Winter)
root: true
distinct_from:
  stw99-problem-ii-nuclear-uct: that asks the UCT for all separable nuclear algebras; this asks it only for strongly self-absorbing ones, where it is equivalent to identifying the known list, and is implied by II.
artifacts:
  - research/artifacts/stw99-master-ledger-2026-08-30.md
  - research/artifacts/ssa-self-kunneth-xiv2-audit-2026-08-31.md
---

**Problem XIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Winter, Abel volume 6.3).  Does every strongly self-absorbing
C\*-algebra satisfy the UCT — equivalently, is every one of them on
the known list (`Z`, UHF of infinite type, `O_2`, `O_∞`, and tensor
products of `O_∞` with UHF)?

## Attempts

* The known reductions localize the problem drastically: an SSA
  algebra is simple nuclear with at most one trace, and by
  Tikuisis--White--Winter-side arguments the finite ones embed into
  `Q_ω` (Problem XIV(1) territory, wired in the graph), while the
  Kirchberg-algebra ones with UCT are classified.  Chern-character
  rigidity: `K_*(D)` is a commutative ring with unit under the
  multiplication induced by `D ≅ D ⊗ D`, and the UCT problem for SSA
  is the first place a UCT-phantom would have to reproduce such ring
  structure — a phantom SSA would give a UCT-violating algebra with
  trivial ideal structure, unique trace or none, and self-absorbing
  KK-ring: the most constrained UCT test class known.  Every route to
  II factors through Kirchberg's `O_2`-absorption reductions, which
  are exactly statements about SSA-adjacent algebras; XIII is the
  honest minimal core of II (route `stw99-ii-implies-xiii`).
* The K-theoretic part is now exact rather than heuristic:
  `ssa-self-kunneth-exact-k-theory-criterion` proves that the external
  product is always split-surjective and that self-Kunneth is equivalent
  to `K_1(D)=0` with `K_0(D)` a torsion-free solid ring. This closes the
  invariant range if self-Kunneth holds, but supplies neither XIV(2)
  embeddability nor XVI uniqueness; those remain independent gates.
