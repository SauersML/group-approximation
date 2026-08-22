---
rg: 2
id: growing-rank-decoder-is-linear-soficity
kind: claim
title: A faithful growing coefficient decoder is exactly linear soficity, not soficity
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
algebra, and by Arzhantseva--Paunescu it is equivalent to linear soficity of
`G` over `k`.

Every such ultraproduct is stably finite.  Therefore a failure of direct
finiteness in `k[G]` forbids every faithful growing-rank decoder.  Conversely,
deriving these decoders uniformly from hyperlinear microstates would prove
`hyperlinear => linear sofic`, not `hyperlinear => sofic`; the latter
conversion is not part of the decoder and cannot be obtained by simply acting
on the underlying finite vector spaces.
