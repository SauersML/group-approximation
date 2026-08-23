---
rg: 2
id: constrained-reynolds-column-has-a-diagonal-scalar-shadow
kind: claim
title: The passive Reynolds cb inverse contains an explicit diagonal signed-incidence inverse
distinct_from:
  exact-passive-jacobian-is-two-reynolds-expectations: that identifies the two noncommutative conditional expectations; this extracts a reducing commutative test space in every left-regular congruence endpoint.
  two-reynolds-l2-gap-does-not-bound-the-cb-normal-inverse: that gives arbitrary high-girth Reynolds columns with a divergent inverse; this identifies the special arithmetic scalar matrices which must actually be bounded or shown divergent.
  passive-iwahori-off-zero-cb-normal-splitting: that asks for the full noncommutative off-zero splitting; this is only a necessary exact-zero scalar condition.
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

In particular, the congruence-level question cannot be settled merely by
noting that each coefficient algebra is finite dimensional: `(DSS5)` is a
uniform completely bounded Green-operator estimate for an explicit growing
family of scalar signed-incidence matrices.  Conversely, `(DSS5)` alone is
not sufficient for the full gate, because off-diagonal matrix coefficients
remain.  The next bounded audit is therefore concrete: prove or refute
`(DSS5)` for the arithmetic coset complexes, before attempting a general
operator-space lifting theorem.

