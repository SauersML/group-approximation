---
rg: 2
id: deligne-central-mark-dies-in-char-p-rank-models
kind: claim
title: For some prime p other than three, every rank model of Deligne's triple cover over characteristic p kills the central mark
refuted_by:
  - deligne-cocycle-has-rank-approximate-projective-representations
distinct_from:
  deligne-central-mark-hs-collapse: that is collapse of the central mark in normalized Hilbert--Schmidt almost representations; this is collapse in rank ultraproducts over fields of characteristic p != 3.
  deligne-twisted-group-algebra-is-not-stably-finite: that asks for a one-sided invertible pair in a twisted group algebra, which implies this through Corollary 2.5 of the twisted-algebras artifact; this asks only that every rank model kill z.
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

**OPEN.** Let `E_3` be Deligne's triple cover of `Sp_4(Z)` with central mark `z`. For some prime `p != 3`, `z` lies in
`Rad_rk,p(E_3)`: every homomorphism from `E_3` into the unit group of a rank ultraproduct of matrix algebras over an
algebraically closed field of characteristic `p` kills `z`.

**Equivalent forms at that p.**
- `E_3` is not `F_p`-linear sofic, since `Rad_rk,p(E_3)` lies in the center.
- The Deligne multiplier has no rank-approximate projective representations in characteristic `p`
  (`deligne-cover-linear-soficity-is-rank-projective-approximation`).
- So this is exactly the negation of `deligne-cocycle-has-rank-approximate-projective-representations`.

**Payoff.** `E_3` would witness `non-linear-sofic-group`.

## Attempts

- **Through the Schur certificate: conditional.** Route `deligne-rank-collapse-via-sp4-schur-kernel` needs
  `sp4-schur-kernel-meets-the-deligne-triple-class` and `schur-kernel-lies-in-char-p-linear-sofic-radical`. The
  second follows from rank root solvability (artifact Section 3). Both are open.
- **Property (T): no help.** It gives no rank rounding over finite fields
  (`kazhdan-group-rank-models-admit-no-expander-decomposition`).
- **Structure of models, positive-side exclusions only.** Any countermodel must be large-block
  (`deligne-rank-models-carry-no-bounded-block-mass`), must have no fixed-level scalar sector
  (`deligne-rank-models-have-no-fixed-level-scalar-sectors`), and cannot come from perturbing exact
  finite-dimensional projective representations (`deligne-rank-realizability-is-invariant-under-fd-class-shifts`).
  These constrain constructions and do not prove collapse.
