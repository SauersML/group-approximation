---
rg: 2
id: kk-counterexample-via-real-rank-zero-host
kind: route
title: A torsion-free group with real rank zero reduced C*-algebra has projections of traces dense in [0,1]
target: kadison-kaplansky-counterexample-exists
requires:
  - torsion-free-real-rank-zero-reduced-cstar-exists
  - torsion-free-trace-defects-are-discrete-or-real-rank-zero
---

Let `Λ` be countable and torsion-free with `RR(C*_r Λ) = 0` (`torsion-free-real-rank-zero-reduced-cstar-exists`).
- `Λ != 1`: `C*_r(1) = C` does have real rank zero, but it is excluded here, because the corollary of
  `torsion-free-trace-defects-are-discrete-or-real-rank-zero` produces a non-discrete trace image, which `C`
  does not have.
- By the proof of (b) ⇒ (a) in that node, the projection traces of `C*_r(Λ)` are dense in `[0,1]`. So some
  projection `e` has `τ(e) ∈ (0,1)`, and `e ≠ 0, 1`.

That is `kadison-kaplansky-counterexample-exists` for `Λ`.
