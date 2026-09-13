---
rg: 2
id: matrix-trace-defect-from-kk-counterexample
kind: route
title: A nontrivial projection of C*_r of a torsion-free group is already a 1x1 trace defect
target: torsion-free-matrix-trace-defect-exists
requires:
  - kadison-kaplansky-counterexample-exists
---

Let `Γ` be torsion-free and `e ∈ C*_r(Γ)` a projection other than `0` and `1`
(`kadison-kaplansky-counterexample-exists`). The canonical trace
`τ(x) = <x δ_e, δ_e>` is faithful, and `e`, `1 - e` are nonzero positive elements, so
`τ(e) > 0` and `τ(1 - e) > 0`. So `τ(e) ∈ (0,1)` is not an integer, and `p = e ∈ M_1(C*_r Γ)`
witnesses `torsion-free-matrix-trace-defect-exists`.
