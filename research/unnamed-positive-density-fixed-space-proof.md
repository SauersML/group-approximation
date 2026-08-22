---
rg: 2
id: unnamed-positive-density-fixed-space-proof
kind: route
title: Apply a finite Fejer kernel to the model-dependent fixed space
target: unnamed-positive-density-fixed-space-is-terminal
requires: []
---

Let `V` be unitary and set `B_N=sum_(j=0)^(N-1)V^j`.  Telescoping gives

```text
||(V^j-1)P||_2<=j epsilon,
||(B_N-N)P||_2<=N(N-1)epsilon/2.                       (UFS4)
```

Since `||NP||_2=N sqrt(tr(P))`, the reverse triangle inequality yields

```text
||B_NP||_2
 >= N sqrt(alpha)-N(N-1)epsilon/2.                    (UFS5)
```

The two domain cuts are Hilbert--Schmidt orthogonal:

```text
||B_N||_2^2=||B_NP||_2^2+||B_N(1-P)||_2^2.
```

Dividing `(UFS5)` squared by `N` proves `(UFS2)`.

Expanding the Fejer polynomial gives

```text
tr(F_N(V))
 =1+2 sum_(k=1)^(N-1)(1-k/N) Re tr(V^k).
```

The sum of the positive coefficients after the leading `1` is `N-1`, so
the stated moment bound proves `(UFS3)`.

Now assume `Gamma` were hyperlinear and take canonical-trace microstates.
Fix `N` with `N alpha>1`.  Because `u` has infinite order, the finitely many
nonidentity words `u^k`, `0<|k|<N`, have canonical trace zero.  Thus their
profile errors give `eta->0`.  The assumed projections give
`epsilon->0` and `tr(P)>=alpha-o(1)`.  The lower bound tends to `N alpha>1`
while the upper bound tends to `1`, a contradiction.

