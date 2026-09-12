---
rg: 2
id: toeplitz-defect-finite-quotient-proof
kind: route
title: The Toeplitz defect spans finitary matrix units, whose infinite simple elementary group dies in residually finite targets
target: toeplitz-defect-dies-in-every-finite-quotient-of-el3
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-model-toeplitz-assembly-2026-09-12.md
---

Section 3 of the artifact.
1. `e = 1 − st` is idempotent with `e s = 0 = t e`, so `e_ab = s^a e t^b` are nonzero matrix units.
2. The root elements `x_ij(λ e_ab)` with `i != j` generate the finitary elementary group on the basis
   `{1,2,3} x N`. Commutators give the same-block transvections, so this group is `SL_fin(F_p)`.
3. `SL_fin(F_p)` is infinite and simple, because no nontrivial scalar survives the union of
   `SL_n(F_p)` over `n >= 3`.
4. In a residually finite target its image is trivial, since residual finiteness passes to
   subgroups and simple residually finite groups are finite.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 42 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
