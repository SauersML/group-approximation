---
rg: 2
id: toeplitz-finite-head-centralizes-deep-tail-proof
kind: route
title: Compute the Toeplitz matrix units and iterate the block-diagonal embedding
target: toeplitz-finite-head-centralizes-deep-tail
requires:
  - toeplitz-head-tail-unital-self-embedding
  - toeplitz-tail-plus-one-swap-generates
---

Write `f=1+xy`. From `yf=fx=0` and `yx=1`,

```text
e_(ij)e_(kl)
 =x^i f y^j x^k f y^l
 =delta_(jk) x^i f y^l
 =delta_(jk)e_(il).                                           (1)
```

Indeed if `j<k`, a positive power of `x` meets `f` on its left; if `j>k`, a
positive power of `y` meets `f` on its right; and if `j=k`, `y^j x^j=1`.
The unilateral-shift representation makes the `e_(ij)` linearly independent,
so `(1)` proves `(TFH1)`.

The augmentation is invariant under `sigma` because `eps(f)=0`. Induction in
`(THT1)` therefore gives

```text
sigma^N(a)
 =x^N a y^N+eps(a)(f_0+...+f_(N-1)),                          (2)
```

which is `(TFH2)`. The first term in `(2)` annihilates every `e_(ij)` with
`i,j<N` on both sides, by the same `yf=fx=0` calculation. The sum of the
first `N` diagonal matrix units is the identity of `F_N`, proving `(TFH3)`.

Finally `sigma^i(s)` is block diagonal on the first `i` coordinates and is
the original head swap on coordinates `i,i+1`. These adjacent
transpositions generate the permutation matrices of every finite head; with
the matrix units already present, any fixed finite matrix packet may be
realized there.

