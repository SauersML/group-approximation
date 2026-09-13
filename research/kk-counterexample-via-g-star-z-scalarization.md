---
rg: 2
id: kk-counterexample-via-g-star-z-scalarization
kind: route
title: A torsion-free matrix trace defect over G becomes a nontrivial projection of C*_r(G * Z)
target: kadison-kaplansky-counterexample-exists
requires:
  - torsion-free-matrix-trace-defect-exists
  - fractional-matrix-trace-gives-projection-in-g-star-z
---

Let `Γ` be countable and torsion-free with a projection `p ∈ M_n(C*_r Γ)` and
`τ_*(p) ∉ Z` (`torsion-free-matrix-trace-defect-exists`). Then `Γ ≠ 1`, since `C*_r(1) = C`
has integer matrix traces. By `fractional-matrix-trace-gives-projection-in-g-star-z`, items 1
and 2:
- `Γ * Z` is countable and torsion-free;
- `C*_r(Γ * Z)` contains a projection `e` with `τ(e) = τ_*(p) - floor(τ_*(p)) ∈ (0,1)`, so
  `e ≠ 0, 1`.

That is `kadison-kaplansky-counterexample-exists` for `Γ * Z`.
