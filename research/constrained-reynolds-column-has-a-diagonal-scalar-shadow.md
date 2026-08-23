---
rg: 2
id: constrained-reynolds-column-has-a-diagonal-scalar-shadow
kind: claim
title: The passive Reynolds cb inverse contains an explicit diagonal signed-incidence inverse
distinct_from:
  exact-passive-jacobian-is-two-reynolds-expectations: that identifies the two noncommutative conditional expectations; this extracts a reducing commutative test space in every left-regular congruence endpoint.
  two-reynolds-l2-gap-does-not-bound-the-cb-normal-inverse: that gives arbitrary high-girth Reynolds columns with a divergent inverse; this identifies the special arithmetic scalar matrices which must actually be bounded or shown divergent.
  right-displacement-reynolds-scalar-cb-complete: that proves this scalar condition is also sufficient for the full cb inverse at exact left-regular endpoints; the present claim only extracts the diagonal restriction.
  passive-iwahori-off-zero-cb-normal-splitting: that asks for the full noncommutative off-zero splitting; even after the exact-zero equivalence, nonlinear continuation away from the endpoint remains open.
---

**ESTABLISHED; EXACT NECESSARY SCALAR CONDITION.**  Let `Q` be a finite
congruence quotient carrying an exact half-parabolic endpoint

```text
(R,S,X),       A=XS^2,       B=XRS,       A^3=B^3=I,   (DSS1)
```

and take the left regular representation on `H=l^2(Q)`.  Identify the
diagonal masa with functions by

```text
M_f delta_q=f(q)delta_q,       L_g f(q)=f(g^(-1)q).
```

The diagonal part of the genuine relative tangent space is exactly

```text
D_E={M_f:L_R f=f, L_X f=-f}.                            (DSS2)
```

Indeed, `[M_f,lambda(R)]=0` is the first equation and conjugation by
`lambda(X)` gives the second.  On this space the exact passive Jacobian is
the completely explicit scalar column

```text
C_Q f=
 (
   (I+L_A+L_A^2)L_(S^(-2))f,
   (I+L_B+L_B^2)L_(S^(-1))f
 ).                                                     (DSS3)
```

Thus `C_Q` is a signed incidence matrix on the finite set of left
`<R>`-cosets, cut to the `X`-odd sector.  It contains no matrix coefficients
or hidden choice of irreducible basis.

More precisely, the diagonal masa is reducing for the Hilbert-space normal
operator of the column.  Every conjugation by a left permutation matrix
preserves diagonal and off-diagonal matrices separately; the same is true
of the `R`-Reynolds projection, the `X`-odd projection, both cubic Reynolds
expectations, their Hilbert adjoints, and hence `DF^*DF`.  Consequently the
Moore--Penrose gauge-normal inverse of the full column preserves `D_E`, and
its restriction is the Moore--Penrose inverse of `(DSS3)` on
`ker(C_Q)^perp`.

For an external multiplicity `m`, matrix-valued diagonal functions give
the amplification

```text
C_Q tensor id_(M_m):
l_infinity(Q/<R>;M_m) ->
l_infinity(Q;M_m) (+) l_infinity(Q;M_m).               (DSS4)
```

It follows that the exact-zero assertion in
`passive-iwahori-off-zero-cb-normal-splitting` necessarily implies

```text
sup_Q ||(C_Q|_(ker C_Q)^perp)^dagger||_cb < infinity.  (DSS5)
```

For the prime-field quotient `Q=PSL_2(F_p)`, put

```text
H=<h(2)>,       N_H=<H,w>,       chi|_H=1, chi(w)=-1. (DSS6)
```

Then `(DSS2)` is canonically the sign-induced module

```text
Ind_(N_H)^Q chi.                                        (DSS7)
```

The two output coordinates of `(DSS3)` lie in the trivial induced modules
from the two order-three subgroups `<A>` and `<B>`.  This identifies the
scalar problem as a finite Hecke/intertwining problem, but also gives an
important firewall against the generic expander analogy.  One input basis
vector is supported on a whole `N_H`-coset, of size `2|H|`; after the cubic
average its incidence degree grows with `|H|`.  Thus `C_Q` is **not** the
bounded-degree cubic coset graph used in
`two-reynolds-l2-gap-does-not-bound-the-cb-normal-inverse`, even though both
maps are built from order-three Reynolds averages.

When

```text
ord_p(4)=(p-1)/2,                                      (DSS8)
```

`H` is the full projective split torus.  The cosets `H\Q` identify with
ordered pairs of distinct points of `P^1(F_p)`, `w` reverses the pair, and
`(DSS7)` is the alternating ordered-pair module (equivalently the
alternating part of the off-diagonal permutation square).  If `(DSS8)`
fails, the extra label has exact size

```text
i_p=(p-1)/(2 ord_p(4)).                                (DSS9)
```

The analogous label can become still larger on composite and prime-power
levels.
Therefore the bounded arithmetic audit leaves one sharply located scalar
frontier: prove a uniform infinity/cb Green estimate for the Hecke columns
`(DSS3)` uniformly in the torus index `(DSS9)` and in the deeper-ring
analogues, or construct a divergent mode in those extra label sectors.
High girth of a bounded-degree graph does not decide this question.

In particular, the congruence-level question cannot be settled merely by
noting that each coefficient algebra is finite dimensional: `(DSS5)` is a
uniform completely bounded Green-operator estimate for an explicit growing
family of scalar signed-incidence matrices.
`right-displacement-reynolds-scalar-cb-complete`
now proves the converse at every exact left-regular endpoint.  Every fixed
right-displacement matrix diagonal is another identical copy of `(DSS3)`,
and the Moore--Penrose inverse is a left-convolution row whose full cb norm
equals its scalar infinity norm.  Thus there is no separate exact-endpoint
off-diagonal audit: prove or refute `(DSS5)` for the arithmetic coset
complexes.  Nonlinear continuation from the zero locus through arbitrary
operator-small passive tuples remains a separate part of
`passive-iwahori-off-zero-cb-normal-splitting`.
