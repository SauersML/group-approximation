---
rg: 2
id: sublinear-julia-seam-rank-proof
kind: route
title: Telescope the rank of every second-copy syllable
target: sublinear-julia-seam-collapses-the-fold-kernel-tracially
requires: []
---

For every `f in F`,

```text
V^*sigma(f)V-sigma(f)
 =V^*sigma(f)(V-1)+(V^*-1)sigma(f).                    (SJP1)
```

Both summands have rank at most `r`, because
`rank(V^*-1)=rank(V-1)=r`. Hence a second-copy syllable differs from its
folded first-copy syllable by rank at most `2r`; a first-copy syllable has
zero difference.

Telescope the products in `(SJS1)`. Multiplication on either side does not
increase rank, and rank is subadditive under addition. With `m` second-copy
syllables this gives

```text
rank(rho(w)-sigma(fold(w)))<=2mr,                      (SJP2)
```

which is `(SJS2)`. If `fold(w)=1`, the two operators in the difference are
unitaries, so its operator norm is at most `2`. For any matrix `X` of rank
`s`,

```text
||X||_(2,d)^2<=s ||X||_op^2/d,
|tr_d(X)|<=s ||X||_op/d.                               (SJP3)
```

Equations `(SJP2)--(SJP3)` give `(SJS3)`.

Finally,

```text
Ad(sigma)(f)V-V
 =sigma(f)(V-1)sigma(f)^*-(V-1).                       (SJP4)
```

This has rank at most `2r` and operator norm at most `2`, proving `(SJS4)`.
Projection of a unit vector onto the orthogonal complement of its original
line is bounded by its total displacement, so `(SJS4)` also gives the stated
almost-reducing conclusion for `C V`. Pointwise quasicentrality on `K`
supplies `(IR2)`, while the same bound at `f_0` rules out `(IR3)`.
