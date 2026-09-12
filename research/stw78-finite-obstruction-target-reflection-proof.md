---
rg: 2
id: stw78-finite-obstruction-target-reflection-proof
kind: route
title: Adjoin one finite quasitrace obstruction and preserve the central-isometry defect
target: stw78-counterexamples-have-finite-obstruction-targets
requires:
  - normalized-quasitraces-detected-finitely
  - oinfty-map-stability-is-central-isometry-splitting
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Since `B` has no normalized 2-quasitrace,
`normalized-quasitraces-detected-finitely` supplies a finitely generated
unital quasitraceless subalgebra

```text
C=C*(1,b_1,...,b_m) subset B.
```

Set `B_0=C*(phi(A),C)`.  It is separable because `A` is separable and only
finitely many generators were adjoined.  A normalized quasitrace on `B_0`
would restrict to one on `C`, so `B_0` remains quasitraceless.  All domain
and map hypotheses are unchanged by corestriction.

Because `phi` is not O-infinity-stable, the central-isometry criterion gives
a finite `F subset A` with `kappa_phi(F)>0`.  Every orthogonal isometry pair
in `B_0` is also such a pair in `B`; shrinking the set over which the
infimum is taken gives

```text
kappa_(phi_0)(F) >= kappa_phi(F)>0.
```

The same criterion proves that `phi_0` is not O-infinity-stable.  Equivalently,
any central copy of `O_infinity` in `(B_0)_infinity` would remain central
after the injective sequence-algebra map `(B_0)_infinity->B_infinity`.
Thus all counterexample properties survive in `B_0`.
