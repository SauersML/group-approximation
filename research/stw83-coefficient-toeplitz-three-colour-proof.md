---
rg: 2
id: stw83-coefficient-toeplitz-three-colour-proof
kind: route
title: Keep the Toeplitz transition scalar and spend two colours on the circle coefficient corner
target: stw83-canonical-circle-toeplitz-dimension-two-bound
requires:
  - stw83-circle-connector-canonical-full-corner
---

Fix `N>=1`, write `E=A_N`, and put `J=K tensor C(T)`.  The quotient map is

```text
pi:E -> C(T),             pi(S^N tensor 1)=u,             (2)
```

where `u` is the coordinate unitary.  We use the two-colour construction from
Brake--Winter, *The Toeplitz algebra has nuclear dimension one*, only for its
explicit quasicentral three-piece decomposition and its finite-dimensional
normal-lifting lemma.  The coefficient-corner step below is new.

## The transition band is still scalar

Choose the usual finite-rank, quasicentral, nested positive contractions
`h_m` for the shift `S^N`, tensored with `1_(C(T))`.  After passing to a
subsequence, write `tilde(h)_m` for the next contraction and arrange

```text
tilde(h)_m h_m=h_m.
```

These form a quasicentral approximate unit for `J` relative to `E`: the shift
commutators tend to zero, and the assertion for `K tensor C(T)` follows by
finite-rank approximation.  Let `mu:C(T)->E` be the Toeplitz cpc section of
(2), obtained by compressing the bilateral `N`-shift.  Crucially,

```text
mu(C(T)) subset C*(S^N,K) tensor 1.                       (3)
```

Use the three compressions

```text
alpha_m(x)=h_m^(1/2) x h_m^(1/2),
beta_m(f)=(tilde(h)_m-h_m)^(1/2) mu(f)
                         (tilde(h)_m-h_m)^(1/2),
gamma_m(f)=(1-tilde(h)_m)^(1/2) mu(f)
                         (1-tilde(h)_m)^(1/2).            (4)
```

The corners containing `alpha_m` are full matrix algebras over the
coefficient circle:

```text
D_m=supp(h_m) E supp(h_m) = M_(r_m)(C(T)).                (5)
```

By contrast, (3) says that every `beta_m(f)` lies in the scalar finite
dimensional subalgebra of its transition corner.  Therefore the
Brake--Winter normal-lifting argument applies without replacing matrices by
matrices over `C(T)`: the lifted normal contractions have finite spectrum,
and their pizza-slice order-zero maps are exactly the original ones.

The rest of that argument is algebraic in (4).  It gives, for a prescribed
finite set and tolerance, a sufficiently large `m`, finite-dimensional
algebras `F^(0),F^(1)`, cpc incoming maps, and cpc order-zero maps

```text
theta^(0):F^(0)->E,
theta^(1):F^(1)->C_m,
C_m=closure((1-tilde(h)_m)E(1-tilde(h)_m)),               (6)
```

such that the sum of the two terms in (6) and `alpha_m` approximates the
identity on the chosen finite set.  Here `theta^(0)` is the merged
transition-band/first quotient colour and `theta^(1)` is the second quotient
colour.  This is precisely the intermediate approximation in the proof of
the Brake--Winter theorem, before their finite-dimensional inner corner is
placed into the second colour.

## Replace the inner corner by two coefficient colours

Equation (5) and matrix stability of nuclear dimension give

```text
dim_nuc(D_m)=dim C(T)=1.
```

Approximate the finite set `alpha_m(F)` through a finite-dimensional algebra
`G^(0) direct-sum G^(1)` with cpc order-zero outgoing maps
`eta^(i):G^(i)->D_m`.  The supporting projection of `D_m` is orthogonal to
`1-tilde(h)_m`: indeed `tilde(h)_m h_m=h_m` makes `tilde(h)_m` equal to one
on `supp(h_m)`.  Hence

```text
eta^(i)(G^(i)) theta^(1)(F^(1))=0.                        (7)
```

The following are therefore three cpc order-zero outgoing maps:

```text
theta^(0),
theta^(1) direct-sum eta^(0),
eta^(1).                                                  (8)
```

Taking the direct sum of the corresponding incoming cpc maps and combining
the two approximation errors proves `dim_nuc(E)<=2`.

Finally, (2) and quotient permanence give

```text
1=dim_nuc(C(T)) <= dim_nuc(E),
```

which proves (1).

This proof also locates the remaining two-colour hinge.  In the scalar
Toeplitz algebra the inner corner is finite dimensional and is put wholly
into the second colour.  Here it is `M_(r_m)(C(T))` and intrinsically needs
two colours.  Only one of those colours is automatically orthogonal to the
transition colour in the Brake--Winter decomposition.  A dimension-one proof
must recolour that second coefficient piece across the transition band; type
I extension permanence and the six-term index do not supply such a
recolouring.
