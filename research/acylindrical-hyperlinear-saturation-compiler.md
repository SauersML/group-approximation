---
rg: 2
id: acylindrical-hyperlinear-saturation-compiler
kind: claim
title: Hull saturation compiles any nonzero normal hyperlinear-killed defect into a 2-generated full-MF-radical quotient
distinct_from:
  common-quotient-onto-normal-subgroup: that claim supplies the small-cancellation quotient and image equality but says nothing about tracial invisibility or MF; this theorem composes it with the abstract detector and records the full-radical semantic output.
  defect-saturation-full-mf-radical: that claim is the explicit Fournier--Facio instance; this theorem applies to every finitely presented torsion-free acylindrically hyperbolic Kazhdan source with a nonzero normal op-to-HS killed subgroup.
  hyperlinear-to-mf-saturation-compiler: that theorem starts from an already supplied routing map; this theorem constructs the map by Hull--Osin small cancellation and records two-generation, finite presentation, torsion-freeness, and acylindrical hyperbolicity.
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - notes/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

Let `E` be finitely presented, torsion-free, acylindrically hyperbolic, and
property-`(T)`.  Let `1 != D triangleleft E` be op-to-HS killed.  For every
finite protected set containing a nonidentity element of `D`, there is a
quotient `q:E->>Q` such that

- `Q` is 2-generated, finitely presented, torsion-free, acylindrically
  hyperbolic, nontrivial, and property-`(T)`;
- the protected set survives;
- `q(D)=Q`;
- `normMFResidual Q = top`;
- every nontrivial quotient of `Q` again has full MF residual and is non-MF.

The reusable division of labor is exact: Hull--Osin supplies `q(D)=Q` and
the finiteness/torsion/AH properties; the saturation compiler supplies the
full MF residual and all quotient consequences.
