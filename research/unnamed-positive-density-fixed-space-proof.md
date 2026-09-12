---
rg: 2
id: unnamed-positive-density-fixed-space-proof
kind: route
title: Apply a finite Fejer kernel to the model-dependent fixed contraction
target: unnamed-positive-density-fixed-space-is-terminal
requires: []
---

Let `V` be unitary, let `X` be a contraction, and set
`B_N=sum_(j=0)^(N-1)V^j`.  Telescoping gives

```text
||(V^j-1)X||_2<=j epsilon,
||(B_N-N)X||_2<=N(N-1)epsilon/2.                       (UFS4)
```

Since `||NX||_2>=N sqrt(alpha)`, the reverse triangle inequality yields

```text
||B_NX||_2
 >= N sqrt(alpha)-N(N-1)epsilon/2.                    (UFS5)
```

The contraction inequality `||B_NX||_2<=||B_N||_2 ||X||<=||B_N||_2`
replaces the orthogonal domain decomposition used in the special case where
`X` is a projection.

Dividing `(UFS5)` squared by `N` proves `(UFS2)`.

Expanding the Fejer polynomial gives

```text
tr(F_N(V))
 =1+2 sum_(k=1)^(N-1)(1-k/N) Re tr(V^k).
```

The sum of the positive coefficients after the leading `1` is `N-1`, so
the stated moment bound proves `(UFS3)`.

Now assume `Gamma` were hyperlinear and take canonical-trace microstates.
Use the supplied `N` with `N alpha>1`.  By `(UFS0)`, the finitely many
nonidentity words `u^k`, `0<|k|<N`, have canonical trace zero.  Thus their
profile errors give `eta->0`.  The assumed contractions give
`epsilon->0` and `||X||_2^2>=alpha-o(1)`.  The lower bound tends to `N alpha>1`
while the upper bound tends to `1`, a contradiction.

For a fixed finite menu, choose an index occurring infinitely often among
the model-dependent successful entries and pass to that subsequence.  The
same `alpha,N` and the corresponding inequalities above are unchanged.
