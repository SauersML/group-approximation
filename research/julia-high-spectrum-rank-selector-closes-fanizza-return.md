---
rg: 2
id: julia-high-spectrum-rank-selector-closes-fanizza-return
kind: route
title: Bound authenticated cutoff rank by the Julia heat amplitude
target: fanizza-heat-filter-one-sided-return
requires:
  - julia-dilation-packages-heat-as-one-cross-gram-moment
  - julia-authenticated-high-spectrum-rank-selector
  - determinant-index-cannot-authenticate-julia-heat-overlap
  - odd-clock-julia-overlap-floor-is-tracial
---

Apply `(AHS4)` to `(AHS2)`.  For fixed `t`, all rounding and microstate
errors vanish, leaving

```text
limsup tr(P) <= C_m/(8 alpha_t t^2).
```

Condition `(AHS3)` sends this bound to zero after taking `t->infinity`.
The established mark-to-carrier estimate then gives the required collapse
of the fixed Fanizza mark.  The two no-go inputs explain why neither an odd
clock nor determinant/index data supplies `(AHS2)`; they do not add another
hypothesis to the positive scalar deduction.
