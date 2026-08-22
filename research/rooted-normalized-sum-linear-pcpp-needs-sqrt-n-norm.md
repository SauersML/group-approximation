---
rg: 2
id: rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm
kind: claim
title: Exact rooted linear proofs of the normalized sum need checker norm at least square root of N
distinct_from:
  uniform-linear-pcpp-tensorizes-to-amitsur-hs: that conditionally tensorizes a uniformly conditioned checker; this proves that the required checker cannot also have uniformly bounded operator norm.
  bounded-expander-flows-cannot-root-the-normalized-amitsur-sum: that proves the obstruction for bounded root occurrence and for divergence-flow encoders; this uses only linearity and exact completeness and applies to every linear extended formulation.
  raw-amitsur-permutation-sampling-has-factorial-gap-loss: that concerns proof-free bounded-query sampling; this permits arbitrary auxiliary linear proof coordinates and obtains a square-root rather than factorial obstruction.
---

ESTABLISHED.  Let `B_N` carry boundary coordinates

```text
b=(t,v_1,...,v_N),
||b||_B^2=|t|^2+(1/N)sum_i |v_i|^2.                    (RNS1)
```

Let `Z_N,C_N` be arbitrary Hilbert spaces and let

```text
D_N:B_N direct_sum Z_N -> C_N                         (RNS2)
```

be linear.  Assume exact completeness in the weak form that the valid
boundary

```text
b_good=(1,N^(-1/2),...,N^(-1/2))                      (RNS3)
```

has some auxiliary proof `z_good` with

```text
D_N(b_good,z_good)=0.                                  (RNS4)
```

If rooted soundness says for every `b,z` that

```text
||D_N(b,z)||_C
 >= kappa_N |t-N^(-1/2)sum_i v_i|,                    (RNS5)
```

then necessarily

```text
||D_N|| >= kappa_N sqrt(N).                            (RNS6)
```

Indeed reuse `z_good` at

```text
b_bad=(1,0,...,0).
```

The rooted error of `b_bad` is one, while linearity and `(RNS4)` give

```text
D_N(b_bad,z_good)
 =D_N(b_bad-b_good,0).
```

But `(RNS1)` gives

```text
||b_bad-b_good||_B^2
 =(1/N) N (1/N)=1/N.
```

Combining this upper bound with `(RNS5)` proves `(RNS6)`.

Consequently no family can simultaneously have exact completeness,
`inf_N kappa_N>0`, and uniformly bounded checker norm.  In particular a
bounded-locality, bounded-weighted-occurrence system with uniformly bounded
coefficients cannot instantiate the scalar object required by
`uniform-linear-pcpp-tensorizes-to-amitsur-hs` whenever those hypotheses give
`sup_N ||D_N||<infinity` in the displayed probability-weighted norms.

The obstruction is geometric, not graph-theoretic: the normalized-sum graph
contains a boundary with root one whose leaf part has norm `N^(-1/2)`.
Therefore a bounded linear map that vanishes there cannot reject the same
root with those leaves deleted by a constant amount, regardless of the
number, topology, or amplitudes of the auxiliary proof coordinates.

