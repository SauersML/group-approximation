---
rg: 2
id: stably-infinite-ring-elementary-groups-have-no-mf-quotient
kind: claim
title: If some multiple of the unit is properly infinite, elementary groups of rank at least twice that multiple have no nontrivial MF quotient
distinct_from:
  full-defect-ring-non-mf-at-rank-two: that needs a properly infinite unit in R itself and gives every rank from two; this needs one only in some M_n(R) and gives every rank from 2n.
  simple-dedekind-infinite-ring-elementary-full-mf-radical: that is the simple, not directly finite case; this adds simple rings that are directly finite but not stably finite, at large rank.
  paradoxical-ring-el-n-full-mf-radical-from-twice-level: that is lane un-middle's independent statement of the same theorem, under the equivalent hypothesis (n+1)[R] <= n[R], with its M_n(R) proof and level calibrations; this is the canonical UN node for the ring-level theorem, by un-architect's ruling of 2026-09-13.
artifacts:
  - research/artifacts/un-paradox-stable-infiniteness-2026-09-13.md
---

Let `R` be a countable unital ring. Write `V(R)` for the monoid of finitely generated projective right
`R`-modules with the algebraic preorder, and `[1] = [R_R]`.

**Theorem.** If `2n[1] <= n[1]` in `V(R)` for some `n >= 1`, then for every `N >= 2n` every
homomorphism from `EL_N(R)` to an MF group is trivial.

**Corollary (simple rings).** If `R` is countable, simple and unital but not stably finite, and
`M_n(R)` is not directly finite, then every homomorphism from `EL_N(R)` to an MF group is trivial for
every `N >= 2n`.

- The hypothesis `2n[1] <= n[1]` is equivalent to a properly infinite unit (condition (PI)) in
  `M_n(R)`.
- The case `n = 1` is `full-defect-ring-non-mf-at-rank-two`.
- The hypothesis fails for every stably finite ring, including every unital subring of an algebraic
  matrix ultraproduct, so the theorem is silent on the Pestov 9.1 side, as it must be.
- For finitely generated `R` and `N >= 3`, `EL_N(R)` is Kazhdan (Ershov–Jaikin-Zapirain), so this
  gives finitely generated Kazhdan groups with no nontrivial MF quotient.
- Not claimed: triviality for `2 <= N < 2n`, and simplicity of `EL_N(R)` modulo its centre.

Proof in the artifact, Sections 1–4 (unreviewed). Independently derived by lane `un-prior-art`.

**Canonical UN node** (un-architect ruling, 2026-09-13). Lane `un-middle` proved the same theorem independently
as `paradoxical-ring-el-n-full-mf-radical-from-twice-level`. Its hypothesis `(n+1)[R] <= n[R]` is equivalent to
`2n[R] <= n[R]` with the same `n`:
- adding `[R]` repeatedly gives `(n+j)[R] <= n[R]` for every `j >= 1`;
- conversely, `(n+1)[R] <= 2n[R]` in the algebraic preorder when `n >= 1`.

Credit both lanes. The UN root `kazhdan-elementary-approximation-type-mirrors-ring-type` cites this node.
