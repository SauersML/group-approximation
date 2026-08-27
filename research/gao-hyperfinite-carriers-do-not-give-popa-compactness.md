---
rg: 2
id: gao-hyperfinite-carriers-do-not-give-popa-compactness
kind: claim
title: Coordinate hyperfiniteness in a Gao carrier does not provide Popa compactness in the ultraproduct
artifacts:
  - research/artifacts/sl3-gao-popa-compactness-audit-2026-08-21.md
distinct_from:
  haagerup-factor-direction-strips-from-property-t-envelope: that has one fixed relative-Haagerup deformation which is compact over a fixed base; a Gao witness supplies different hyperfinite coordinate approximations whose ranks may diverge.
  gao-re-witness-carries-orthogonal-arithmetic-hecke-tower: that transports the arithmetic correspondences through a hypothetical RE witness; this audits the deformation needed to rule out the witness.
---

Let

```text
P=L(SL_3(Z)) subset calB=prod_omega B_k,
```

where every `B_k` is hyperfinite.  Popa's rigidity-versus-Haagerup theorem
cannot be applied from these hypotheses alone.  It requires a sequence of
completely positive maps on ONE ambient algebra whose `L^2` implementations
are compact (over the chosen base) and converge pointwise to the identity.
Coordinatewise finite-dimensional approximations to the `B_k` need not
induce compact operators on `L^2(calB)`: their ranks can, and for an embedded
diffuse property-`(T)` factor must, escape every uniform bound.

This failure is structural.  Residual finiteness of `SL_3(Z)` gives a
trace-preserving embedding

```text
P -> prod_omega M_(d_k),
```

even though every coordinate is finite dimensional.  If coordinate
hyperfiniteness automatically produced Popa's scalar-compact approximation
on the ultraproduct, property `(T)` would make convergence uniform on the
unit ball of `P`; a compact operator cannot uniformly approximate the
identity on the unit ball of an infinite-dimensional `L^2(P)`.

Thus neither property `(T)` nor the word "hyperfinite" in Gao's definition
gives a positive-corner intertwiner.  A proof needs an additional UNIFORM
coordinate-complexity estimate; bare QWEP and hyperfiniteness do not contain
one.
