---
rg: 2
id: measure-free-ample-groupoid-el-n-full-mf-radical-proof
kind: route
title: A normalized state on V(A_k(G)) restricts to an invariant measure; Tarski then gives a paradoxical level
target: measure-free-ample-groupoid-el-n-full-mf-radical
requires:
  - kmp-tarski-theorem-preordered-monoids
  - paradoxical-ring-el-n-full-mf-radical-from-twice-level
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md
---

Artifact §4.

1. **A state gives a measure.** Let `ν` be a state on `V(R)` with `ν([R]) = 1`. Put `m(U) = ν([1_U R])` for compact open
   `U ⊆ X`.
   - Disjoint unions give direct sums, so `m` is additive; it is monotone, with `m(X) = 1`.
   - For a compact open bisection `B`, `1_B 1_{B^{-1}} = 1_{r(B)}` and `1_{B^{-1}} 1_B = 1_{s(B)}`, so
     `1_{r(B)}R ≅ 1_{s(B)}R` and `m(r(B)) = m(s(B))`.
   - `X` is compact and zero-dimensional, so `m` is countably additive on the clopen algebra and extends to an invariant
     Borel probability measure.
2. **Tarski.** With no invariant measure, `V(R)` has no state at `[R]`, so `[R]` is paradoxical by
   `kmp-tarski-theorem-preordered-monoids`: `(n+1)[R] ≤ n[R]` for some `n`.
3. **Ring theorem.** `paradoxical-ring-el-n-full-mf-radical-from-twice-level` gives the conclusion for `N ≥ 2n`.
4. **Finitely generated case.** If `R` is finitely generated and `N ≥ 3`, `elementary-groups-over-fg-rings-have-property-t`
   gives property (T) of `EL_N(R)`. It is finitely generated since `R` is.
