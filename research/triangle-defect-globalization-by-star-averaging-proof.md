---
rg: 2
id: triangle-defect-globalization-by-star-averaging-proof
kind: route
title: Choose a maximum star-degree line and use that affine pair itself as the label list
target: triangle-defect-globalizes-to-a-bounded-label-list
requires: []
artifacts:
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
---

For a star relation `S subset B x B`, put

```text
d(b) = Pr_(c uniform in B)[(b,c) in S].
```

Product-uniform density at least `1-eta` says

```text
E_b d(b) = |S|/|B|^2 >= 1-eta.
```

Choose `b_0` with `d(b_0) >= 1-eta` and put `Q=C_(b_0)`.  A star certificate
for `(b_0,c)` contains a point of `C_(b_0) intersect C_c`, so `Q` hits at
least a `1-eta` fraction of the family.  In the affine application `C_(b_0)`
has exactly two points.  Hence `L=2` and `gamma=1-eta`, with no dependence on
the alphabet dimension.

For sampling without replacement, give each diagonal pair `(b,b)` a star
certificate before applying the same argument.  Its product-uniform density
is

```text
[|B| + |B|(|B|-1)(1-eta)]/|B|^2 >= 1-eta,
```

and the conclusion is unchanged.
