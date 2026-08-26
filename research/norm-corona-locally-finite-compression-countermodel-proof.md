---
rg: 2
id: norm-corona-locally-finite-compression-countermodel-proof
kind: route
title: Implement the one-sided tensor shift and its surviving Pauli defect in one corona group
target: norm-corona-locally-finite-compression-countermodel
requires:
  - uhf-cyclic-shift-has-strict-compressed-commutant
---

Use the UHF embedding and cyclic tensor shifts of the prerequisite.  Let
`P_j` be the finite Pauli group on the first `j` tensor factors and put

```text
L=union_j iota(P_j),                 c=[(c_n)_n].      (1)
```

Then `cLc^(-1)=sigma(L)<L`.  Take

```text
l_0=iota(Z tensor 1),       c'=c^(-1)l_0c,       l=iota(X tensor 1). (2)
```

Coordinatewise `c'` is the last-site `Z`.  It commutes eventually with
every fixed initial Pauli word, so `c' in C_G(L)`.  Moreover

```text
cc'c^(-1)=l_0,
[cc'c^(-1),l]=iota([Z,X])=-1_Q.                       (3)
```

The scalar in `(3)` has norm distance two from the identity and hence
survives in `Q`.

The last-site copy `D_n=M_2` commutes with every fixed initial stage, so its
corona class lies in `L' intersect Q`.  But `c^(-1)Lc` contains the
last-site `Z`; the last-site `X` fails to commute with it by norm two.
This proves the strict relative-commutant inclusion.  With normalized
Hilbert--Schmidt norm the same commutator has norm two at every coordinate,
which proves the asserted failure for the asymptotic commutant.

Finally `G` is a quotient of the ascending HNN extension `L*_sigma`.  In
that extension

```text
union_(k>=0) t^(-k)Lt^k
```

is a normal locally finite group and the quotient is infinite cyclic.
Thus the extension is locally-finite-by-cyclic and amenable, as is `G`.
