---
rg: 2
id: tangent-green-rank-payment-proof
kind: route
title: Spectrally truncate the hard tangent tail and integrate the soft part
target: tangent-green-divergence-is-flexibly-rank-paid
requires:
  - gauge-optimized-target-has-uniform-congruence-tangent-gap
  - normalized-hs-taylor-remainder-is-not-dimension-free
  - low-rank-reflection-surgery-preserves-the-exact-bs-core
---

The first prerequisite gives, on the normal tangent quotient,

```text
||Ch||_2 >= sigma ||h||_2.                              (TGR1)
```

If the fixed `k` output rows of `Ch` have operator norm at most `epsilon`,
their normalized Hilbert--Schmidt norms are at most `epsilon`; hence
`||h||_2<=sqrt(k)epsilon/sigma`.  This proves `(TGD3)` and shows that packing
such modes on disjoint supports cannot retain positive Hilbert--Schmidt
mass without violating `(TGR1)`.

For each coordinate, let `p_j=1_(theta,infinity)(|h_j|)`.  Markov's spectral
inequality and `(TGR1)` give

```text
sum_j tr(p_j)
 <= theta^(-2)||h||_2^2
 <= theta^(-2)sigma^(-2)||Ch||_2^2.                   (TGR2)
```

The soft coordinate `(1-p_j)h_j(1-p_j)` has operator norm at most `theta`.
Because `p_j` is spectral for `|h_j|`, changing its exponential changes any
fixed presentation word only on a fixed word-length multiple of
`sum_j rank(p_j)`.  The cited low-rank surgery ledger therefore pays the
hard tail by exactly the flexible-rank bound `(TGR2)`.

Finally the second prerequisite supplies the true mixed Taylor estimate

```text
||F(rho exp(h))-Ch||_2 <= L ||h||_op ||h||_2.
```

On the soft part, `theta<=sigma/(2L)` and `(TGR1)` yield

```text
||F(rho exp(h))||_2 >= (sigma/2)||h||_2,
```

which is `(TGD5)`.  Thus every divergent operator-norm Green mode is either
Hilbert--Schmidt negligible or confined to the explicitly rank-paid hard
tail, as claimed.
