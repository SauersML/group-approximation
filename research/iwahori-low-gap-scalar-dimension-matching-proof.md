---
rg: 2
id: iwahori-low-gap-scalar-dimension-matching-proof
kind: route
title: Apply approximate Hall rounding to the localized overlap transport
target: iwahori-low-gap-scalar-dimension-matching
requires:
  - mixed-intertwiner-energy-transport-localization
  - fractional-overlap-approximate-hall-rounding
---

By mixed-intertwiner transport localization, the overlap mass on forbidden
pairs satisfies

```text
beta_n=sum_(lambda_(n,i,j)>=a_n) m_(n,i,j)
      <= E_n/a_n -> 0.
```

Apply `fractional-overlap-approximate-hall-rounding` with the low-gap pairs as
the allowed graph.  It returns integer edge flows matching at least

```text
d_n-ceil(beta_n d_n)
```

dimensions on each side.  Since `ceil(beta_n d_n)/d_n <= beta_n+1/d_n`, this
is `d_n-o(d_n)` whenever `d_n->infinity`; bounded dimensions are harmless,
because along a vanishing-defect sequence one may pass to the eventual exact
subsequence or absorb the bounded discrepancy into the flexible stabilization.
Hence the unmatched normalized dimension tends to zero, as claimed.