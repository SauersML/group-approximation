---
rg: 2
id: rooted-normalized-sum-linear-pcpp-needs-sqrt-n-norm
kind: claim
title: Exact rooted linear proofs of the normalized sum need square-root checker norm even on unitary leaves
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

## The obstruction persists on scalar unitary leaves

The preceding witness used leaves of modulus `N^(-1/2)`.  Restricting
soundness and completeness to unitary leaf coordinates does not repair the
problem.  Take `N=k^2`, `k>=3`.  Let `v_good` contain `k` copies of `1` and
split its remaining `N-k` entries equally between `i` and `-i`.  Then every
leaf is unitary and

```text
N^(-1/2) sum_j (v_good)_j=1.                           (RNS7)
```

Put `epsilon=arcsin(1/(k-1))`.  Keep the `1` entries fixed, replace every
`i` by `i exp(i epsilon)`, and replace every `-i` by
`-i exp(-i epsilon)`.  Call the resulting unitary vector `v_bad`.  Each of
the `N-k` rotated entries has real part `-sin(epsilon)`, while their imaginary
parts cancel.  Hence

```text
sum_j (v_bad)_j
 =k-(N-k)/(k-1)=0.                                    (RNS8)
```

Moreover `|exp(+-i epsilon)-1|<=2/(k-1)`, so

```text
||(0,v_bad-v_good)||_B^2
 <=4(N-k)/(N(k-1)^2)
 =4/(k(k-1)).                                         (RNS9)
```

If exact completeness supplies `z_good` for `(1,v_good)`, reuse it at
`(1,v_bad)`.  The latter has rooted error one by `(RNS8)`, while linearity,
`(RNS9)`, and soundness give

```text
||D_N|| >= (kappa_N/2)sqrt(k(k-1))
          =Omega(kappa_N sqrt(N)).                    (RNS10)
```

Thus even a checker required to work only on scalar unitary boundary points
cannot have constant rooted gap and bounded norm.  The surviving nonlinear
route must change the checker itself or discretely quantize configurations;
merely adding unitary constraints around the same linear extended
formulation does not evade the square-root barrier.
