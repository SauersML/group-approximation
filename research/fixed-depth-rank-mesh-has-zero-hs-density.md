---
rg: 2
id: fixed-depth-rank-mesh-has-zero-hs-density
kind: claim
title: Fixed-depth rank quantization has zero normalized-HS density
distinct_from:
  additive-index-instability: that rules out unnormalized additive indices under amplification; this quantifies why a fixed number of corner-renormalized rank steps cannot turn the rank lattice into a positive normalized-HS floor.
  finite-depth-contractive-computation-ladder: that is a valid scalar endpoint once a positive-density recurrence is supplied; this rules out supplying that recurrence from rank-mesh granularity alone.
---

Fix a depth `m`, a rational finite packet, and `0<lambda<1`.  Suppose the
only strictness in a proposed normalized multiplicity comparison is that a
nonzero integral numerator has absolute value at least one.  In dimension
`d`, after clearing the fixed packet denominators, this gives at most a mesh
scale

```text
C/d.                                                             (FRM1)
```

Propagating it through `m` corner-renormalized steps changes this only by the
fixed factor `lambda^(-m)`.  Hence its strongest possible density scale is

```text
C lambda^(-m)/d -> 0.                                           (FRM2)
```

The same conclusion is forced by tensor amplification.  Replacing a packet
representation by its `k`-fold amplification preserves all normalized-HS
defects and trace densities, while the normalized rank mesh becomes
`1/(kd)`.  A fixed number of renormalizations cannot distinguish these
amplifications by a positive constant.

Thus finite-depth contraction remains valid only when every step already has
a dimension-free **positive-density** comparison.  Integrality or corner-rank
quantization alone cannot supply it.  A viable matrix-only input must instead
produce extensive mismatch before normalization, use depth growing with the
dimension, or invoke a theorem such as a global cross-context capacity gap
which is unavailable to the exact tracial completeness model.

