---
rg: 2
id: shared-label-arm-anchor-closes-thompson-a6-seam
kind: route
title: Apply the shared-endpoint cancellation estimate at every adjacent Thompson chart
target: thompson-v-r5-a6-seam-pointwise-synchronization
requires:
  - bleak-quick-a6-seam-exposes-shared-label-arm-anchor
  - shared-endpoint-r2-r3-anchor-has-linear-seam-bound
---

Use `(BQA1)` and either `(BQA2)` or `(BQA3)` for each shared occurrence.
The shared-endpoint theorem gives

```text
||X_i-X_i'||_2 <= C delta
```

after changing the universal constant.  Multiplying by the common pivot and
using `(BQA1)` gives

```text
||Y_i-Y_i'||_2 <= C' delta,
```

which is `(A6S2)`.  The local chart construction included in the anchor
claim retains `(A6S1)`.  All estimates use only a bounded number of cells and
therefore have constants independent of dimension and packet size.

