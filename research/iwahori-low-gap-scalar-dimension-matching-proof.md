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
d_n-floor(beta_n d_n)
```

dimensions on each side.  Since

```text
floor(beta_n d_n)/d_n <= beta_n -> 0,
```

the unmatched normalized dimension tends to zero with no assumption on the
growth rate of `d_n`.  This is exactly the claimed `d_n-o(d_n)` scalar
matching.