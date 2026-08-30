---
rg: 2
id: stw78-two-finite-witness-normal-form-proof
kind: route
title: Apply the Blackadar--Handelman matrix criterion to the finite quasitrace seed
target: stw78-counterexamples-have-two-finite-witnesses
requires:
  - stw78-counterexamples-have-finite-obstruction-targets
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Use `stw78-counterexamples-have-finite-obstruction-targets` to obtain a
finitely generated unital subalgebra `C subset B_0` with no normalized
2-quasitrace and a finite `F subset A` with
`kappa_(phi_0)(F)>0`.

The Blackadar--Handelman matrix criterion says that a unital C-star algebra
admits a normalized 2-quasitrace if and only if no matrix algebra over it
has properly infinite unit.  Since `C` has no normalized 2-quasitrace, the
unit of `M_n(C)` is properly infinite for some finite `n`.  Choose the least
such `n`; minimality gives the asserted failure of proper infiniteness at
all lower levels.  Choose two orthogonal isometries witnessing proper
infiniteness of `1_(M_n(C))`.

If necessary, append the finitely many matrix entries of the isometry to the
displayed generating tuple.  They already belong to `C`, so neither `C` nor
`B_0` changes.  The finite central-defect witness is unaffected.  This gives
both asserted finite witnesses in one corestriction.

The conversion from absence of quasitraces to proper infiniteness at a
finite matrix level is exactly the imported Blackadar--Handelman matrix
criterion; all localization and simultaneous-witness assertions are
internal.
