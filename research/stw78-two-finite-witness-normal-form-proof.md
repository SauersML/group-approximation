---
rg: 2
id: stw78-two-finite-witness-normal-form-proof
kind: route
title: Apply Blackadar--Handelman to the finite quasitrace obstruction seed
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

The Blackadar--Handelman theorem says that every stably finite unital
C-star algebra admits a normalized 2-quasitrace.  Its contrapositive shows
that `C` is not stably finite.  Hence some finite matrix algebra `M_n(C)`
contains a nonunitary isometry.  Choose the least such `n`; minimality gives
finiteness of all lower matrix levels.

If necessary, append the finitely many matrix entries of the isometry to the
displayed generating tuple.  They already belong to `C`, so neither `C` nor
`B_0` changes.  The finite central-defect witness is unaffected.  This gives
both asserted finite witnesses in one corestriction.

The conversion from absence of quasitraces to failure of stable finiteness
is exactly the imported Blackadar--Handelman theorem; all localization and
simultaneous-witness assertions are internal.
