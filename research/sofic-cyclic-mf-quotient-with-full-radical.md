---
rg: 2
id: sofic-cyclic-mf-quotient-with-full-radical
kind: claim
title: A finitely presented sofic Powers group has only cyclic MF quotients and an intrinsic full MF radical
distinct_from:
  cyclic-mf-quotient-phase-transition: Here the ambient group is sofic and a Powers group, with an explicit infinite-order deciding word and an intrinsic full MF radical.
  torsion-free-sofic-exact-mf-radical-over-z: This kernel is not finitely generated and contains A_5; it does not supply the torsion-free property-T kernel required there.
  finite-block-perfect-lamps-have-exact-mf-radical: That radical is itself residually finite; the HNN extension here has an intrinsic full MF radical and a cyclic visible quotient.
artifacts:
  - research/artifacts/sofic-cyclic-mf-quotient.md
---

There is an explicit finitely presented sofic acylindrically hyperbolic
Powers group P with split quotient chi:P->Z and an infinite-order word d
such that N=ker(chi)=normalClosure_P(d)=Rad_MF(P)=Res_fin(P), and
Rad_MF(N)=N. The kernel is nontrivial, perfect, and not finitely generated.
For every normal R in P, Rad_MF(P/R)=NR/R and P/R is MF if and only
if d belongs to R, equivalently P/R is cyclic. Its reduced C*-algebra is
simple with a unique tracial state; its profinite completion is Z-hat.

The explicit finite presentation adds s and s(tx^-1)s^-1=a t b t^-1
to the affine A_5 finite-block group of Theorem F, with x the cyclic
coordinate matrix, a=(12)(34), and b=(123) in the root lamp. The full
written proof is in the artifact. No new Lean verification is asserted.
