---
rg: 2
id: linear-tree-braid-sigma-via-connolly-doig-raag
kind: claim
title: "Explicit BNSR invariants of braid groups of linear trees on any number of strands"
distinct_from:
  tree-braid-sigma-for-at-most-three-strands-and-radial-trees: that claim settles trees with n <= 3 and radial trees, where the braid groups are free; this asks for all n on linear trees, where the braid groups are right-angled Artin groups with commuting generators
---

For every linear tree `T` (all essential vertices on one embedded arc) and
every `n`, give an explicit defining graph `Λ(T,n)` with `B_nT ≅ A_{Λ(T,n)}`,
and with it the complete BNSR invariants `Σ^m(B_nT)` through the
Meier–Meinert–VanWyk living-subgraph criterion.

## Attempts

- 2026-09-13 (z1-08-graph-braid): the input is Connolly–Doig,
  arXiv:math/0411368, Theorem 1.5, read from the PDF. For a tree `X`, an
  endpoint `p` and an interval `I` containing `p` and every node, "for each
  integer n ≥ 0 there is a right angled Artin presentation ⟨β(n);R(n)⟩ for
  B_n(X;I) such that ι_p(β(n−1)) ⊂ β(n) and ι_{p∗}(R(n−1)) ⊂ R(n)". The
  presentation is built inductively (stars first, then van Kampen gluing),
  not as an explicit graph. An alternative route to the defining graph:
  Farley–Sabalka's presentation (arXiv:math/0410539 Theorem 5.3, with the
  embedding choice described in the proof of Theorem 5.11 of
  arXiv:math/0602444, "left as an exercise"). Its generators are critical
  1-cells, and they commute exactly as the critical 2-cells dictate. Once
  `Λ` is explicit, the key test is connectivity. A disconnected `Λ` makes
  `B_nT` a free product, so `Σ¹ = ∅`. A connected `Λ` gives `Σ¹ ≠ ∅` through
  characters nonzero on all generators. The expected dividing line is
  whether particles at distinct essential vertices can be exchanged
  independently, which needs `n ≥ 4` and two essential vertices. Not yet
  attacked in detail.
