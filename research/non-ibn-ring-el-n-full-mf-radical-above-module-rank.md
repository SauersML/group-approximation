---
rg: 2
id: non-ibn-ring-el-n-full-mf-radical-above-module-rank
kind: claim
title: If R^m is isomorphic to R^(m+d), every homomorphism from EL_N(R) to an MF group is trivial for all N >= max(m+1, 3)
distinct_from:
  paradoxical-ring-el-n-full-mf-radical-from-twice-level: that needs only stable paradoxicality and gives rank 2n; this needs an exact failure of IBN and lowers the rank to m+1 by conjugating EL_(N+jd) into EL_N.
  binary-leavitt-all-ranks-full-mf-radical: that reaches every rank for L_(F_2)(1,2) through prefix codes; this reaches rank m+1 for every ring of module type (m, m+d), including m >= 2.
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13-part2.md
---

Let `R` be a countable unital ring with `R^m ≅ R^{m+d}` for some `m ≥ 1` and `d ≥ 1`. Then every homomorphism from
`EL_N(R)` to an MF group is trivial for every `N ≥ max(m+1, 3)`.

- Instances: every Leavitt algebra of module type `L_k(m, m+d)`. For `L_k(2,3)` the conclusion holds for every `N ≥ 3`.
  Over a finite field `k`, with `elementary-groups-over-fg-rings-have-property-t`, these are finitely generated Kazhdan groups with no nontrivial
  MF quotient.
- Recalled, not verified: `L(m,n)` with `m ≥ 2` is a domain (Cohn), so the ring is directly finite. That lies outside
  `cor:simple-infinite-ring`.

**Review (un-verify, 2026-09-13): PASS after scope repair.** The conjugation `Φ(g) = AgB` through `R^M ≅ R^N` with a free coordinate, the product formulas, the commutator isolating `e_{kc′}(1)` and normal generation re-derived; `L_k(2,3)` gives `N ≥ 3`; Cohn and Bergman enter only as remarks. Scope: finite generation and (T) of `EL_N(L_k(2,3))` need `k` finite (a field finitely generated as a ring is finite), and the instance bullet now says so. See `research/artifacts/un-review-2026-09-13-part4.md` §2.
