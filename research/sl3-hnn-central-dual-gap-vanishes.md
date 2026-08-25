---
rg: 2
id: sl3-hnn-central-dual-gap-vanishes
kind: claim
title: Stable-letter-central dual tuples have no positive SL3 matrix-range separation gap
distinct_from:
  sl3-large-prime-hnn-matrix-range-capture: that is the primal assertion that the selected lattice tuple approaches the ucp matrix range; this is its strictly restricted dual form after central-letter averaging, quantifying only over uniformly bounded separators asymptotically commuting with the HNN letter.
  hnn-matrix-range-obstruction-is-a-letter-multiplicity-coupling: that proves a positive-gap separator must live off the intrinsic spectral algebra; this is the open arithmetic assertion that even the remaining multiplicity-commutant separator has nonpositive gap.
  single-hecke-average-isometry-for-lambda-central-unitaries: that tests one primal lattice-central unitary under one fixed arithmetic Hecke average; this tests every bounded dual generator tuple in the stable-letter commutant against the support function of the full group matrix range.
---

Fix `p>=11` and the data `Lambda`, `Gamma`, `G_p`, `S` of
`sl3-large-prime-hnn-matrix-range-capture`.  Let
`phi_n:G_p->U(d_n)` be a canonical hyperlinear approximation, put
`X_(n,s)=phi_n(s)` and `T_n=phi_n(t)`, and write

```text
h_n(B)=sup_(Y in MR_(d_n)(Lambda,S))
       Re sum_(s in S)tr_(d_n)(B_s^*Y_s).                         (LCG1)
```

For every tuple sequence `B_n=(B_(n,s))_s` satisfying

```text
sum_s||B_(n,s)||_2^2=1,
sup_(n,s)||B_(n,s)||_op<infinity,
sum_s||T_nB_(n,s)T_n^*-B_(n,s)||_2^2 ->0,                         (LCG2)
```

the claim is

```text
limsup_n [ Re sum_s tr_(d_n)(B_(n,s)^*X_(n,s))-h_n(B_n) ] <=0.    (LCG3)
```

By `central-letter-averages-matrix-range-separators`, `(LCG3)` implies
`sl3-large-prime-hnn-matrix-range-capture`: any positive primal distance
would yield a uniformly operator-bounded tuple obeying `(LCG2)` with a
fixed positive gap, contradicting `(LCG3)`.  Thus this is the smallest
currently isolated UCP lemma closing the large-prime HNN route.  It no
longer asks to correct an arbitrary lattice microstate, or even to test all
dual directions; it asks only that the stable-letter commutant contain no
positive matrix-range separator for the selected lattice tuple.

## Attempts

- `hnn-matrix-range-obstruction-is-a-letter-multiplicity-coupling` removes
  the intrinsic `W^*(T)` part: a positive-gap tuple must have definite
  off-spectral mass in `T' cap M`.  Hence scalar Fourier analysis of the
  Haar letter cannot settle `(LCG3)`.
- Property T cannot act directly on `B_n`: the lattice tuple is still an
  almost-representation, while `B_n` centralizes the stable letter rather
  than a genuine lattice representation.  Producing a Stinespring actor at
  this point would already prove the desired matrix-range inequality.
- The weighted Rayleigh no-go
  `balanced-leak-saturates-weighted-rayleigh-tests` concerns one scalar
  coefficient of a primal projection.  Here `h_n(B)` is a complete-matrix-
  order support function; the missing datum is a host relation forcing its
  multiplicity-commutant component to pay.
- On the near-genuine face `(LCG3)` follows from the established exact-face
  collapse at `p>=11`.  Therefore any counterexample is simultaneously a
  uniform lattice outlier and a bounded nonabelian stable-letter-
  multiplicity Choi separator.  No existing arithmetic type decomposition
  applies before that outlier is exactified.
