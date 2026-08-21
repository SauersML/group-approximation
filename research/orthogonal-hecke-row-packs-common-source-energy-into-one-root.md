---
rg: 2
id: orthogonal-hecke-row-packs-common-source-energy-into-one-root
kind: claim
title: Pack the entire common-source covariance energy into one Steinberg root coefficient
distinct_from:
  gauge-pair-holonomy-needs-one-source-moment: that reduces the decoder to a finite sum of mixed Hecke covariance norms; this packages that sum as the norm of one coefficient row.
  affine-leavitt-steinberg-hs-coefficient-decoder: that asks for a decoder for the full affine-Leavitt coefficient system; this isolates one fixed coefficient and one root word for the Fanizza cell.
  rational-unitary-additive-dilation-is-trivial: that rules out a fixed rational unitary dilation representing addition functorially; this uses orthogonal matrix units only to preserve an already-defined squared norm and makes no unitary-dilation claim.
---

Let the finite list of common-source covariance defects from `(GFM7)` be

```text
D_j=a_j V_j^*Q-V_j^*QZ_j,             1<=j<=m,          (OHR1)
```

where `m` is fixed by the four-context Fanizza packet.  In one fixed matrix
amplification choose matrix units `(E_(rs))_(1<=r,s<=m)` and form the single
row coefficient

```text
R_Q=sum_(j=1)^m E_(j1) tensor D_j.                      (OHR2)
```

Then exactly

```text
R_Q^*R_Q
 =E_(11) tensor sum_j D_j^*D_j,                         (OHR3)
```

and, for normalized matrix trace,

```text
m ||R_Q||_2^2=sum_j||D_j||_2^2=M_Q.                    (OHR4)
```

Thus the whole common-source row is one positive Gram scalar.  The matrix
units may be supplied by any fixed finite packet with an `M_m(C)` simple
corner; the amplification factor `m` is constant and independent of the
eventual matrix dimension.

## One root word

In a finitely presented coefficient ring containing the finite Hecke
expressions in `(OHR1)`, name the coefficient `(OHR2)`.  The Steinberg root

```text
x_(12)(R_Q)                                               (OHR5)
```

is one ordinary group word after the usual finite ring-to-Steinberg
translation.  Therefore a sufficient ordinary-word endpoint for the
Fanizza common-source cell is the single-coordinate estimate

```text
||R_Q(U)||_2^2
 <=K ||x_(12)(R_Q)(U)-I||_2^2+o(1),                    (OHR6)
```

or the weaker version with total defining-relator energy on the right.  By
`(OHR4)`, `(OHR6)` is precisely `(GFM9)`, hence gives `NCL13`.

This does not assert `(OHR6)`.  It proves that no full coefficient-ring
decoder is logically required for this lane.  The remaining Steinberg
interface consists of one fixed coefficient row and one fixed root word.

## Rectangular-escape audit

The one-root formulation does not by itself defeat rectangular escape.
`common-source-leavitt-cell-inherits-rectangular-root-escape` gives exact
finite paired-label tables in which label dimension expands while
multiplicity contracts.  Such a model can satisfy all fixed root
multiplication identities without realizing the coefficient row as an
operator on the same reservoir.  Consequently `(OHR6)` must still be proved
by a matrix-coordinate boundary/same-reservoir argument; it cannot be inferred
merely from the formal identity defining `(OHR5)`.

The gain is exact claim size: the required boundary theorem need only
authenticate the `L^2` norm of the one row `(OHR2)`, not reconstruct the
Leavitt algebra, all context blocks, or a multiplicative coefficient map.

## Exact completeness

When the HALT forbidden carrier `Q` vanishes, `R_Q=0`.  More generally, an
exact gauge-covariantized common-source model has every `D_j=0`, hence again
`R_Q=0`.  Naming `(OHR5)` therefore adds no tracial-extension requirement to
the exact witness.  The obstruction in `(OHR6)` is finite-dimensional-only,
as required.
