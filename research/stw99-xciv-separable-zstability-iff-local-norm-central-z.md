---
rg: 2
id: stw99-xciv-separable-zstability-iff-local-norm-central-z
kind: claim
title: Separable Z-stability is exactly local operator-norm centralization of Z
distinct_from:
  stw99-hyperfinite-factor-property-si: that claim works in tracial relative ultrapowers and still needs a norm-lifting argument; this equivalence is stated entirely in the original C*-algebra and operator norm.
  stw99-xciv-commuting-car-seed-has-zstable-hull: that is an exact-commutation sufficient condition for one seed; this is an equivalence using approximate commutation for every finite set.
---

Let `B` be any unital C\*-algebra, with no separability assumption.  The
following are equivalent.

1. Every norm-separable subset of `B` is contained in a separable unital
   `Z`-stable C\*-subalgebra of `B`.
2. For every finite `F subset B`, finite `G subset Z`, and `epsilon>0`, there
   is a unital homomorphism `phi:Z->B` such that

```text
||[a,phi(z)]|| < epsilon       (a in F, z in G).
```

Consequently Problem XCIV is precisely an operator-norm local-centralization
problem inside `R`.  Replacing the displayed norm by the tracial `2`-norm is
not enough.
