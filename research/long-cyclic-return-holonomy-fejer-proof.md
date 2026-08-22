---
rg: 2
id: long-cyclic-return-holonomy-fejer-proof
kind: route
title: Apply the finite Fejer kernel inside the reducing holonomy corner
target: long-cyclic-return-holonomy-annihilates-every-carrier
requires:
  - unnamed-positive-density-fixed-space-is-terminal
---

Put

```text
a_n=tau_n(E_n)^(-1)||X_n||_(2,n)^2,
epsilon_n=tau_n(E_n)^(-1/2)||(A_n-1)X_n||_(2,n).
```

By `(LCH1)` and `(LCH3)`'s hypothesis, `epsilon_n->0`.  Fix `N`.  The Fejer
estimates `(UFS2)--(UFS3)` apply unchanged to this rectangular left module.
Indeed `X_n=E_nX_n` and contractivity give `X_nX_n^*<=E_n`; the lower
telescoping estimate uses only left multiplication by `A_n`, while the upper
estimate is bounded by the Fejer trace in `E_nM_nE_n`.  Hence

```text
N (sqrt(a_n)-(N-1)epsilon_n/2)_+^2
 <=1+(N-1) max_(1<=|k|<N)|tau_(E_n)(A_n^k)|.           (LCHF1)
```

Using `(LCH2)` and taking `limsup` yields

```text
limsup_n a_n<=1/N.
```

Since `N` is arbitrary, `a_n->0`.  Finally

```text
||X_n||_(2,n)^2=tau_n(E_n)a_n<=a_n,
```

which proves `(LCH3)`.  A regular cyclic shift of order `d_n` has zero
normalized trace in every nonzero power of magnitude below `d_n`, so
`d_n->infinity` implies `(LCH2)`.
