---
rg: 2
id: norm-corona-locally-finite-compression-countermodel-proof
kind: route
title: Implement the one-sided tensor shift by a corona unitary and read the Pauli commutator
target: norm-corona-locally-finite-compression-countermodel
requires: []
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
---

Write `M_(2^n)=M_2^(tensor n)` and embed each initial tensor block compatibly
by `iota_(j,n)(x)=x tensor 1_(2^(n-j))`.  Its coordinate sequence defines an
injective unital map `iota:M_(2^j)->Q`.

Let `P_j` be the finite Pauli group on the first `j` tensor factors and put

```text
L=union_j iota(P_j),                 c=[(c_n)_n].      (1)
```

Here `c_n` cyclically moves the last tensor factor to the first.  Consequently

```text
c iota(x)c^(-1)=iota(1_2 tensor x),
```

so `cLc^(-1)<L`; first-site `X` is outside the image, with a fixed positive
operator-norm distance at every larger tensor level.  Take

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
