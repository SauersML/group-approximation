---
rg: 2
id: minimal-packet-corner-overlap-has-irreducible-spectator-dilution
kind: claim
title: A minimal packet corner loses its old-commutant overlap to an irreducible spectator
distinct_from:
  packet-kazhdan-commutant-placement-decouples: that leaves the full positive-density Reynolds defect on an independent tensor factor; this computes the smallest rank-one coefficient and its amplified corner against two old-group actions with identical packet data.
  nested-packet-reynolds-defect-is-orthogonal-to-old-commutant: that gives exact orthogonality for the whole nested Reynolds difference; this shows that passing to one minimal idempotent does not repair the density problem.
  commutant-density-forces-bounded-type-mass: that characterizes positive total old-commutant density by bounded old types; this gives an explicit fixed-packet overlap calculation exhibiting the loss by a factor `m^(-2)`.
---

Let `B` be a finite packet group with an irreducible representation `pi` of
dimension `n`, and let `p` be a minimal matrix idempotent in its `pi` block.
Let `K` be a group with irreducible unitary representations `sigma_m` of
unbounded dimensions `m`, and put `Lambda=B times K`.  On

```text
H_m=C^n tensor C^m,          d=nm,
P=p tensor I_m,
```

compare the two exact representations

```text
rho_m^flat(b,k)=pi(b) tensor I_m,
rho_m^irr(b,k)=pi(b) tensor sigma_m(k).                 (MCO1)
```

Their restrictions to every packet word are identical, and the minimal
packet carrier has the same Hilbert mass

```text
q=rank(P)/d=1/n.                                        (MCO2)
```

Let `C_P` be the orthogonal projection of the adjoint Hilbert space onto
the amplified corner `P End(H_m) P`, and let `E_flat,E_irr` be the
orthogonal projections onto the two `Lambda` commutants.  With normalized
adjoint trace `tr_ad=Tr_End/d^2`,

```text
tr_ad(E_flat C_P)=1/n^3,
tr_ad(E_irr C_P)=1/(n^3 m^2).                           (MCO3)
```

More generally, if `rho:Lambda->U(H)` has dimension `d`, `P` is any
projection, and `mu` is Haar measure on the compact closure of
`rho(Lambda)`, then the overlap is the exact character second moment

```text
tr_ad(E_Lambda C_P)
 =d^(-2) integral |Tr(P rho(g))|^2 d mu(g).             (MCO3b)
```

In particular, if `rho` is irreducible and `rank(P)=qd`, Schur
orthogonality gives

```text
tr_ad(E_Lambda C_P)=q/d^2.                              (MCO3c)
```

Thus the same positive packet mass and the same exact Schur word table can
have either constant corner overlap or overlap tending to zero.  The full
corner amplification retains density only by retaining the external
multiplicity algebra in the old commutant.

The still smaller carrier consisting of the single adjoint vector `P` has
rank one in an adjoint space of dimension `d^2`.  Hence its normalized
adjoint density is exactly

```text
1/d^2=1/(n^2m^2),                                      (MCO4)
```

before any old-commutant constraint is imposed.  A scalar overlap for one
minimal coefficient therefore cannot by itself supply the `Omega(q^2)`
range required by `(PCD1)`.

Consequently the existing local Schur relations cannot force positive
old-commutant density from a minimal idempotent or rank-one coefficient.
A live compressed-coefficient actuator must additionally authenticate the
external multiplicity action--equivalently, prevent it from becoming an
unbounded irreducible old-`K` type.  This is the same bounded-type promotion
burden as `(PCD1)`, now visible in the smallest possible corner.
