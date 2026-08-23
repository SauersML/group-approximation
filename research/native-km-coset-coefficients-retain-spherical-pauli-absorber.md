---
rg: 2
id: native-km-coset-coefficients-retain-spherical-pauli-absorber
kind: claim
title: The unreduced native Kac--Moody coset coefficients retain a spherical Pauli absorber
distinct_from:
  three-reynolds-plus-kernel-energy-has-vanishing-gap: that scalarizes the three overlap maps to Reynolds expectations; this writes the actual finite coset-incidence coefficient maps for the (2,4,6) rank-three presentation and proves that their common spherical block reduces to the same Pauli operator.
  fixed-finite-label-km-holonomy-is-scalar-or-gapped: that excludes nonscalar fixed-label relator twists; this absorber is scalar on the finite label coordinate and noncommutative only in the growing multiplicity coordinate.
  finite-group-intertwiner-laplacian-gap: that gives a gap off the exact finite-group intertwiner space; this identifies a positive-density exact trivial-label intertwiner space on which every native coefficient map acts scalarly.
---

**ESTABLISHED.**  For the explicit Kac--Moody Cartan matrix with Coxeter
types

```text
(m_12,m_13,m_23)=(2,4,6),                              (NKC1)
```

let `P_0<=P_i<=P_ij` be its finite standard parabolics over `F_q`.  The
unreduced coefficient maps between the regular rank-two chart and its two
rank-one faces are the normalized coset-incidence maps

```text
R_(ij,i):ell^2(P_ij/P_0)->ell^2(P_ij/P_i),
(R_(ij,i)f)(gP_i)
 =|P_i:P_0|^(-1/2) sum_(xP_0 subset gP_i) f(xP_0),     (NKC2)
```

and likewise for `j`, together with their adjoints and finite products.
These are the concrete restriction coefficients before passing to Reynolds
projections or relator norms.

Each map in `(NKC2)` sends the normalized constant coset vector to a scalar
multiple of the normalized constant coset vector.  Consequently the full
three-vertex coefficient system has a common reducing spherical summand

```text
C 1_sph tensor M_m,                                    (NKC3)
```

on which **every** native finite-label coefficient is scalar and the entire
matrix algebra `M_m` is invisible.  This summand occurs in every regular
chart with fixed positive normalized density (for example the trivial
isotypic summand of `lambda_(P_ij) tensor I_m` has density `1/|P_ij|`).
It therefore cannot be discarded as `o(d)` when `q` is fixed and
`m->infinity`.

The finite labels do have a genuine orthogonal gap.  On the `B_2` leg
`P_13`, the incidence graph is the generalized quadrangle of order `(q,q)`.
If `N_13` is its point-line incidence matrix, then

```text
spec(N_13 N_13^*)={(q+1)^2,2q,0},                     (NKC4)
```

so the normalized nonconstant incidence coefficient is at most

```text
sqrt(2q)/(q+1)<1.                                      (NKC5)
```

Thus the corresponding two-range angle Laplacian has gap at least
`1-sqrt(2q)/(q+1)` off the constants.  Formula `(NKC5)` excludes a rotating
Pauli fiber in every nonspherical finite-label sector, but says nothing on
`(NKC3)`.

There is a completely native way to insert the Pauli rotation.  Choose a
spanning tree in the bipartite coset graph

```text
L_13=(P_13/P_1) union (P_13/P_3),  edges=P_13/P_0.
```

Its `r=q^4` chords give the free kernel basis from the `B_2` quotient
`P_1*_(P_0)P_3->P_13`.  Gauge every tree edge and every chord but one by the
identity on `(NKC3)`, and gauge the remaining chord by the Pauli word

```text
Y_t=AD_tAD_t.                                           (NKC6)
```

All local `P_12,P_13,P_23` group tables remain exact regular tables, every
unreduced coefficient map `(NKC2)` is satisfied exactly on the label
coordinate, and the actual native free-kernel coefficients are `I` except
for the selected basis coefficient `Y_t`.  On the multiplicity plane
`span_R{B,C}`, its positive word operator is exactly

```text
(I-Ad(Y_t))^*(I-Ad(Y_t))=4sin^2(4t)I.                  (NKC7)
```

Every unreduced finite-label term vanishes on this plane because it acts
scalarly on `(NKC3)`.  Hence the full native coefficient operator has
positive spectral value at most

```text
4sin^2(4t)->0.                                         (NKC8)
```

This is a native-coefficient counterpacket: retaining the full finite coset
maps improves the orthogonal label sectors but does **not** exclude the
rotating Pauli fiber on the canonical regular chart.  Any surviving
Kac--Moody coercive inequality must include an authenticated coefficient
whose compression to the spherical label summand acts nontrivially on the
multiplicity algebra.  No `P_ij`-equivariant finite-label restriction map
can do this, by the one-dimensionality of the trivial representation.
