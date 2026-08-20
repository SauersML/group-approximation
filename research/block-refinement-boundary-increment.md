---
rg: 2
id: block-refinement-boundary-increment
kind: claim
title: Refining one projection charges exactly twice its internal cut boundary
---

Let `U` be unitary and let `q,r` be orthogonal projections with `p=q+r`.
Then, in normalized Hilbert--Schmidt norm,

```text
||[U,q]||_2^2+||[U,r]||_2^2
 = ||[U,p]||_2^2 + 2 ||[pUp,q]||_2^2.                (BRI)
```

Thus the increase in total block-boundary energy caused by splitting `p` into
`q` and `r` is measured entirely inside the old block.  The identity also
holds after summing over any finite family of unitaries.
