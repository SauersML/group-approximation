---
rg: 2
id: rectangle-five-seven-retains-only-three-incidence-types
kind: claim
title: A rectangle five-by-seven inverse pair retains only three partner incidence types
distinct_from:
  five-seven-partner-has-five-eulerian-incidence-types: that gives five types for an arbitrary C3-fixed partner; this uses the factor's outside-normalizer rectangle to eliminate the two all-normalizer types.
  normalizer-five-seven-is-three-by-four-f4-crossed-product: that treats a factor supported inside the normalizer; this treats the complementary factor with one outside-normalizer rectangle.
  minimal-five-seven-partner-cannot-escape-support-subgroup: that confines support to the factor subgroup without using double-coset separation; this excludes two confined support geometries by separating normalizer and nonnormalizer product terms.
artifacts:
  - research/artifacts/five-seven-coefficient-and-adjoint-audit-2026-08-21.md
---

Let

```text
alpha=h_0+(1+r)x(1+s),       x notin N_G(H).
```

If the seven-term partner is supported in `N_G(H)`, then `h_0 beta` is
normalizer-supported while every term of `(1+r)x(1+s)beta` is outside the
normalizer.  The two summands cannot cancel, and `alpha beta=1` would force
`h_0 beta=1`, impossible at support seven.  Therefore the two all-normalizer
incidence types are excluded.  Exactly three types remain:

```text
m=3:  one 4-cycle;
m=1:  one 6-cycle, or one 4-cycle plus one 2-cycle.
```

The 2-cycle is a doubled normalizer cell; each surviving longer cycle has an
outside-normalizer edge.

