---
rg: 2
id: punctured-congruence-imprimitivity-proof
kind: route
title: Put one trivial line into the identity atom of every congruence partition
target: punctured-congruence-imprimitivity-is-only-flexibly-exact
requires: []
---

Write `H_a=l^2(Q_a) direct_sum C r_a`, where `r_a` spans the last
one-dimensional summand.  For `j<=a`, let `R_(a,j,y)` be the projection in
`l^2(Q_a)` onto

```text
span{delta_x : x mod 2^j=y}.
```

Define

```text
P_(a,j,e)=R_(a,j,e)+r_a,       P_(a,j,y)=R_(a,j,y)  (y!=e).         (PCP1)
```

These are orthogonal projections summing to one.  Reduction fibers nest,
so summing `(PCP1)` over a fiber of `Q_j -> Q_i` gives `(PCP1)` at level
`i`; the extra line always remains in the identity atom.

On the regular summand left translation is exactly covariant.  The trivial
summand is fixed by every `sigma_a(c)`, whereas the label of its atom is
moved from `e` to `c mod 2^j`.  If `c=1 mod 2^j`, there is no error.  If
`c!=1 mod 2^j`, precisely two labelled differences contain the rank-one
projection `r_a`, once with each sign.  With normalized Hilbert--Schmidt
norm,

```text
sum_y ||sigma_a(c)P_(a,j,y)sigma_a(c)^*-P_(a,j,cy)||_2^2
 =2 tr_(d_a)(r_a)=2/d_a,                                (PCP2)
```

proving `(PCI2)`.

For fixed `c!=1`, residual finiteness of the principal congruence tower
gives `c mod 2^a !=1` for all sufficiently large `a`.  The regular
character then vanishes at `c`, while the trivial line contributes one:

```text
tr_(d_a)(sigma_a(c))=1/(|Q_a|+1)->0,                    (PCP3)
```

which proves `(PCI3)`.

Suppose `(E_y)_(y in Q_j)` were an exact covariant PVM for `sigma_a`.
Reduction `C -> Q_j` is onto, so transitivity and unitary conjugacy give
`rank(E_y)=r` independent of `y`.  Since the projections sum to the
identity,

```text
d_a=sum_y rank(E_y)=|Q_j|r.                              (PCP4)
```

But the reduction `Q_a -> Q_j` is onto, so `|Q_j|` divides `|Q_a|` and
cannot divide `|Q_a|+1`.  This contradiction proves `(PCI4)`.

Finally remove `C r_a`.  The remaining representation is exactly
`lambda_(Q_a)`, and the families `(R_(a,j,y))` are exact covariant nested
PVMs for every `j<=a`.  The removed normalized rank is `1/d_a->0`, proving
the flexible-exact statement and completing the proof.
