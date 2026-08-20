---
rg: 2
id: block-refinement-boundary-increment-proof
kind: route
title: Expand the unitary into q, r, and outside-p matrix blocks
target: block-refinement-boundary-increment
requires: []
---

Write `o=1-p` and expand `U` into the orthogonal three-by-three block matrix
for `q+r+o=1`.  The commutator with a projection contains exactly the two
matrix directions crossing that projection.  Hence

```text
||[U,p]||_2^2
 = ||oUq||_2^2+||oUr||_2^2+||qUo||_2^2+||rUo||_2^2.
```

The sum of the two refined commutators contains those same four outside terms
once, and the two internal directions twice:

```text
||[U,q]||_2^2+||[U,r]||_2^2
 = ||[U,p]||_2^2
   +2(||rUq||_2^2+||qUr||_2^2).
```

But `[pUp,q]` has precisely the orthogonal blocks `rUq` and `-qUr`, so its
squared Hilbert--Schmidt norm is their squared-norm sum.  This is `(BRI)`.
