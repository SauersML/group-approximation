---
rg: 2
id: vanishing-corner-reduction-map-proof
kind: route
title: Localize a sharp k-positive reduction map on a trace-negligible matrix corner
target: vanishing-corner-reduction-maps-defeat-tracial-cp-upgrade
requires: []
---

The Choi matrix of the unnormalized map

```text
L_(k,r)(X)=k Tr(X)I_r-X
```

is

```text
C_(k,r)=k I_r tensor I_r-|Omega_r><Omega_r|,             (VCR4)
Omega_r=sum_(i=1)^r e_i tensor e_i.
```

If `xi` is a unit vector of Schmidt rank at most `m`, then

```text
|<Omega_r,xi>|^2 <= m.                                  (VCR5)
```

Hence `(VCR4)` is `m`-block positive for every `m<=k`, so `L_(k,r)` and its
positive scalar normalization `(VCR1)` are `k`-positive.  For

```text
xi_(k+1)=(1/sqrt(k+1)) sum_(i=1)^(k+1) e_i tensor e_i,
```

the expectation in `(VCR4)` equals `k-(k+1)=-1`.  Thus the map is not
`(k+1)`-positive.  Direct calculation gives

```text
R_(k,r)(I)=I,
Tr(R_(k,r)(X))=Tr(X),                                   (VCR6)
```

proving all assertions about `(VCR1)`.

Block pinching is ucp and trace preserving.  Its composition with
`id_(M_N) direct-sum R_(k,r)` is therefore unital, trace preserving, and
`k`-positive.  If `(VCR2)` were `(k+1)`-positive, composing with the completely
positive inclusion of the lower `M_r` corner and compression back to that
corner would make `R_(k,r)` `(k+1)`-positive, a contradiction.

For a block-diagonal contraction, only the lower block moves.  Both `X_11`
and `R_(k,r)(X_11)` have operator norm at most one (a unital positive map has
norm one), so their unnormalized Hilbert--Schmidt distance is at most
`2 sqrt(r)`.  Division by `sqrt(D)` proves `(VCR3)`.

Finally, evaluating a word of fixed length `ell` on two contraction tuples
which differ by at most `epsilon` in normalized `2`-norm changes the word by
at most `ell epsilon`, by telescoping.  Thus `(VCR3)` makes the hidden corner
invisible to every fixed arithmetic word atlas while its explicit Schmidt-
rank witness continues to detect failure of complete positivity.

