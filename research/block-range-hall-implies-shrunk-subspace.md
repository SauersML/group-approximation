---
rg: 2
id: block-range-hall-implies-shrunk-subspace
kind: claim
title: A Hall deficit in block range-spans certifies a shrunk operator subspace
---

Let

```text
H = direct_sum_(i in I0) H_i,
K = direct_sum_(j in J0) K_j
```

be finite-dimensional Hilbert spaces, and let `S <= Hom(H,K)` be any linear
operator space.  For source block `i` and target block `j`, define the
**block range-span**

```text
R_(j,i) = span{ p_j T x : T in S, x in H_i } <= K_j,
```

where `p_j` is the target-block projection.  For a subset `A <= I0`, put

```text
R_j(A) = sum_(i in A) R_(j,i).
```

If for some source-block set `A`

```text
sum_(i in A) dim(H_i) - sum_j dim(R_j(A)) >= r,        (BRH1)
```

then `S` has an `r`-shrunk subspace.  More precisely, for

```text
X = direct_sum_(i in A) H_i
```

one has

```text
dim(X) - dim(S(X)) >= r,                              (BRH2)
```

where `S(X)=span{T x:T in S,x in X}`.

This criterion is strictly finer than a zero/nonzero block-support Hall test:
a nonzero rectangular block may still have a small collective range-span, and
`(BRH1)` sees that finite-rank spectral information.  It is deliberately only
a sufficient condition for general noncommutative-rank deficiency; if it
fails, a shrunk subspace may still exist at a non-coordinate input subspace.
