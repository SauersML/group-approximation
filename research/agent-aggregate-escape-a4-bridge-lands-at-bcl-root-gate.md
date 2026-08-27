---
rg: 2
id: agent-aggregate-escape-a4-bridge-lands-at-bcl-root-gate
kind: claim
title: The A4 displacement bridge gives four positive overlaps but no fixed conditional coefficient idempotent
distinct_from:
  central-sign-bcs-atoms-are-subgroup-reynolds-projections: That identifies a forbidden assignment with a Reynolds projection; this splits its mass among four order-three Fourier overlaps.
  agent-a4-bridge-transfers-forbidden-mass-but-stops-at-root-kill: That records the same displacement bridge and the failure of literal root identification; this isolates the additional support-polynomial failure in the Bass--Serre amalgam.
---

Let `H` be one forbidden Reynolds subgroup, let `J` be the central sign, and
put

```text
E=e_H Q_-,                 Q_-=(1-J)/2.                (ABR1)
```

Choose `h in H` and attach the standard `A4` triangle with order-three
elements `z_1,z_2` and involution `b`, identifying

```text
z_1 z_2=b=hJ.                                           (ABR2)
```

Assuming `g=hJ` has order exactly two, this has an ordinary Bass--Serre
realization by amalgamating the old group with `A4` over `<g>=<b>`.  Both
factors embed.  On `E`,

```text
(hJ)E=-E,
||(z_1z_2-1)E||_2^2=4 tau(E).                          (ABR3)
```

The triangle inequality gives

```text
||(z_1-1)E||_2^2+||(z_2-1)E||_2^2 >=2 tau(E).          (ABR4)
```

Put `R_(i,omega)` for the `omega` spectral projection of `z_i`, where
`omega` is either nontrivial cube root of unity.  Since `z_i^3=1`,

```text
||(z_i-1)E||_2^2
 =3 sum_(omega!=1) tau(E R_(i,omega)).                 (ABR5)
```

Combining `(ABR4)--(ABR5)`, one of the four pairs `(i,omega)` satisfies

```text
tau(E R_(i,omega))>=tau(E)/6.                          (ABR6)
```

This conclusion is exact and dimension-independent.  It is, however, an
overlap statement, not a fixed packet projection.  The Bass--Serre bridge
group is

```text
<H,J> *_(<hJ>) A4,
```

which is generally infinite (and virtually free when the factors are
finite).  Therefore the positive contraction

```text
R_(i,omega) E R_(i,omega)                              (ABR7)
```

does not lie in a fixed finite-dimensional bridge algebra.  Its support in a
particular von Neumann representation is representation-dependent and need
not be a polynomial in `(ABR7)` with presentation-uniform degree.  Taking
that support, or its central support, consequently does **not** produce a
fixed coefficient-ring idempotent which can be named in an ordinary finite
group presentation.  Earlier versions of this node incorrectly asserted
that the whole bridge algebra was finite-dimensional; `(ABR1)--(ABR6)` are
the maximal valid conclusion.

Literal root identification also fails.  In a perfect tracial model the
forbidden projection `E` vanishes, but the global word `hJ` need not be the
identity.  Identifying both order-three letters with algebraically killed BCL
roots would force `hJ=1` globally and destroy perfect completeness.

Thus the valid front end is only

```text
forbidden Reynolds mass
 -> one of four explicit positive A4 Fourier overlaps. (ABR8)
```

Even after the padded free-compressor row algebraically kills a named
coefficient root `x(P)`, the sole missing implication is a
**payload-to-root coupling**: convert one of `(ABR7)` into nontrivial spectrum
of `x(P)`, with dimension-uniform control, while preserving the perfect
tracial model when `E=0`.  The A4 calculation alone does not do this.

DERIVATION
agent-aggregate-escape-a4-fourier-corner-proof
