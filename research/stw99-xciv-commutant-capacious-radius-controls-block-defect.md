---
rg: 2
id: stw99-xciv-commutant-capacious-radius-controls-block-defect
kind: claim
title: Distance to a commutant-capacious core bounds the fixed-block defect
distinct_from:
  stw99-xciv-finite-dimensional-radius-controls-block-defect: that theorem restricts the approximating cores to finite-dimensional algebras; this theorem permits arbitrary nonnuclear and non-type-I cores provided their ambient relative commutant contains the fixed block.
  stw99-xciv-commuting-car-seed-has-zstable-hull: that theorem requires exact containment of an entire separable seed in a core with a commuting CAR copy; this theorem is local and quantitative for norm neighborhoods of any core with one commuting I_(2,3) copy.
  stw99-xciv-some-finite-tuple-has-positive-fd-radius: that theorem proves finite-dimensional cores cannot approximate every tuple; the enlarged radius here supplies a logically independent route to zero block defect.
  stw99-xciv-finite-norm-spectral-gap-is-negative-certificate: that theorem uses distance to scalars controlled by commutators with a fixed test; this theorem uses distance of the test itself to subalgebras with large relative commutant.
artifacts:
  - research/artifacts/stw99-xciv-commutant-capacity-audit-2026-08-30.md
---

Call a unital C*-subalgebra `A subset R` **D-capacious**, for
`D=I_(2,3)`, if `A' intersect R` contains a unital copy of `D`.  For finite
`F subset R`, define

```text
beta_D(F)=inf_A max_(a in F) dist(a,A),                  (3)
```

where `A` ranges over all unital D-capacious subalgebras.  Then

```text
gamma_D(F)<=2 beta_D(F).                                (4)
```

The radius `beta_D` is no larger than the finite-dimensional radius
`alpha_R`, but can use genuinely infinite-dimensional cores.  For example,
under any tensor decomposition

```text
R=R_0 tensor_bar R_1,
```

both tensor legs are D-capacious.  Consequently

```text
gamma_D(F)<=2 max_(a in F) dist(a,R_0 tensor 1),         (5)
```

and symmetrically for the other leg.  Every finite tuple contained in, or
arbitrarily norm-close to varying, proper tensor legs therefore has zero
fixed-block defect, with no finite-dimensional approximation assumption.

Conversely a negative certificate `gamma_D(F)>=delta` must obey

```text
beta_D(F)>=delta/2.                                     (6)
```

Thus it must stay uniformly far not only from matrix algebras but from every
subalgebra possessing a commuting fixed dimension-drop block.

This does not show that `beta_D(F)=0` for arbitrary finite `F subset R`.
That assertion is a strictly broader norm tensor-splitting problem.
