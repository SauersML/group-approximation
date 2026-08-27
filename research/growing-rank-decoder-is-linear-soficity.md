---
rg: 2
id: growing-rank-decoder-is-linear-soficity
kind: claim
title: A faithful growing coefficient decoder is linear soficity of the coefficient algebra
distinct_from:
  hs-steinberg-root-kernel-is-linear-sofic: that asks for this decoder for one quotient extracted from one HS representation; this identifies the abstract approximation property obtained if such decoders exist.
  hyperlinear-implies-sofic: that asks for permutation approximations from arbitrary unitary approximations; this lands only in normalized-rank matrix approximations, an a priori weaker target than soficity.
  matrix-cyclotomic-lift-obstruction: that excludes exact coefficient-faithful lifts in every finite matrix size; this classifies the remaining approximate growing-size escape.
artifacts:
  - research/artifacts/matrix-cyclotomic-lift-and-rank-decoder-audit-2026-08-21.md
---

For a field `k` and countable group `G`, asymptotically unital `k`-linear maps

```text
theta_n:k[G] -> M_(d_n)(k)
```

that are asymptotically multiplicative in normalized rank and retain positive
normalized rank on every nonzero element are exactly an embedding of `k[G]`
into a rank-metric matrix ultraproduct.  This is linear soficity of the
`k`-algebra.  Restriction to the group basis makes `G` linear sofic over `k`.
For `k=C`, Arzhantseva--Paunescu prove the converse; their theorem does **not**
supply the converse for `k=F_2`.

Every such ultraproduct is stably finite.  Therefore a failure of direct
finiteness in `k[G]` forbids every faithful growing-rank decoder.  For
`k=F_2`, deriving these decoders uniformly from hyperlinear microstates would
prove the stronger coefficient-sensitive implication
`hyperlinear G => F_2[G] linear sofic`, hence direct finiteness of `F_2[G]`.
It is not merely the group-class implication `hyperlinear => linear sofic`,
and neither implication is the same as `hyperlinear => sofic`.
