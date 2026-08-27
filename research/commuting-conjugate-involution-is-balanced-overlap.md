---
rg: 2
id: commuting-conjugate-involution-is-balanced-overlap
kind: claim
title: Native commuting-conjugate projective energy is exactly a balanced projection-overlap scalar
distinct_from:
  commuting-conjugate-involution-transfer-for-sl3-pair: that asks to exclude interior overlap in arithmetic matrix microstates; this proves only the exact two-projection reduction and the tracial firewall.
---

For a trace-zero self-adjoint involution `c` commuting with `h c h^-1`, put

```text
P=(1-c)/2,       Q=hPh*,       a=tr(PQ).
```

Then `P,Q` are commuting trace-half projections and

```text
1-|tr(c h c h^-1)|^2=8a(1-2a).
```

Projective scalarity is therefore exactly the dichotomy `Q=P` or `Q=1-P`
(approximately in the approximate version).  The coset Bernoulli model has
`a=1/4`, so the interior-overlap obstruction exists in an exact finite
tracial von Neumann algebra and must be excluded by a matrix-coordinate
argument.
