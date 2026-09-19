---
rg: 2
id: full-center-hnn-transport-cancels-schur-multiplicity-proof
kind: route
title: Restrict central sectors to the Pauli edge and exhibit the regular-flow countermodel
target: full-center-hnn-transport-cancels-schur-multiplicity
requires:
  - support-failure-packet-has-explicit-hs-payment
artifacts:
  - experiments/schur_packet_hnn_flow_search.py
---

Write central elements and characters as vectors in `F_2^3`, paired by
`k(z) = (-1)^(k dot z)`.  An edge isomorphism carrying the center by `T`
pulls a target character `k'` back to `T^t k'`; this proves `(FHC2)`.  The
stable-letter unitary conjugates the corresponding central spectral
projections.  It therefore maps `H_k` unitarily onto `H_(k')`, proving equality
of their Hilbert dimensions.

On the `k`-sector of `A_(r,c)`, the two noncentral generators have commutator
phase `(-1)^(k dot ell_(r,c))`.  If this phase is minus one, their algebra is
`M_2(C)`.  With the central character fixed it has a unique simple module of
dimension two.  Hence its multiplicity in `H_k` is exactly `dim(H_k)/2`.
The target phase is also minus one because

```text
k dot ell = (T^t k') dot ell = k' dot (T ell).
```

This proves `(FHC3)` and the cancellation assertion.

For completeness, evaluate `(FHC1)` at `k=(j,e,f)`.  The ambient commutation
matrix is

```text
[[j,j+e],[f,0]],
```

so the packet dimensions over the eight characters are

```text
000:1, 001:2, 010:2, 011:4,
100:2, 101:4, 110:2, 111:2.                            (1)
```

The nine nonzero row/column pairs in `(FHC1)` realize exactly the six
nontrivial commutator words

```text
001,010,011,100,101,110.                               (2)
```

The exhaustive `GL_3(F_2)` verifier checks all 168 central automorphisms.  It
finds involutions pairing `101` with each character in `(FHC4)` while carrying
one word in `(2)` to another.  One especially small forbidden-to-harmless chart
is

```text
T=[[1,0,1],[0,1,0],[0,0,1]],
ell_source=001, ell_target=101,
101 <-> 100.                                           (3)
```

The script prints explicit matrices and row/column witnesses for all five
rank-one targets.  Since the six sectors in `(FHC4)` together with `101` are
orthogonal and each chart equates its target mass to the `101` mass, their
total mass is at least six times the forbidden mass.  This proves `(FHC5)`.

Finally, the fundamental group of any finite graph of finite groups is
virtually free and residually finite.  The vertex group `B_sub` embeds, so a
finite quotient can be chosen injective on it.  The regular representation of
that quotient is an exact finite-dimensional model; restricted to `B_sub` it
contains copies of the regular representation and therefore has positive mass
in every central character, including `101`.  All graph relators nevertheless
have zero energy.  This is an exact countermodel to any proposed positive
forbidden-mass payment derived solely from the stated full-center charts.
