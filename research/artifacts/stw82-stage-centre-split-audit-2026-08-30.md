---
title: STW LXXXII stage-centre split-extension checkpoint (2026-08-30)
---

# Exact maximum for stage-centre split AF extensions

## Statement

For a unital split extension

```text
0 -> I -> E -> D -> 0,
```

suppose an increasing finite-dimensional exhaustion `(D_n)` of the AF
quotient satisfies

```text
[s(Z(D_n)),I]=0
```

at every stage.  Then `dim_nuc(E)=dim_nuc(I)`.  Since `D` is AF, this is
the desired maximum formula.

The automatic special case is substantial: every unital split extension
with UHF quotient satisfies the formula, with an arbitrary ideal and an
arbitrarily noncentral action of the section on that ideal.

## Where the extra colour disappears

At a finite stage, the lifted central block units split both the middle
algebra and ideal into matching direct sums.  Within a quotient block
`M_r`, lifted matrix units give exact identifications

```text
middle block ~= M_r(unitization(J)),
ideal block  ~= M_r(J)
```

for the same corner `J`.  Matrix amplification and minimal unitization do
not change nuclear dimension.  Thus the finite quotient stage is not
approximated by a separately labelled order-zero colour at all; it is
absorbed algebraically into the unitizations of the ideal corners.

## Relation to previous positive classes

The existing AF split-centralizer theorem assumes `[s(D),I]=0`.  For a
noncommutative simple quotient block that hypothesis actually forces its
ideal corner to vanish.  The stage-centre theorem instead requires only
commutation of block units.  Matrix units may act nontrivially on the
ideal, and the ideal need not vanish.

For example, if `D` is UHF, `J` is any nonunital C*-algebra, and

```text
E=D tensor unitization(J),       I=D tensor J,
```

then the canonical section generally does not commute with `I`, while the
stage-centre condition is automatic and the theorem gives the exact
maximum.  No projectional quasicentral approximate unit or quasidiagonal
extension hypothesis enters the proof.

## Boundary

For a general finite-dimensional stage with several simple summands, its
central block projections may fail to commute with the ideal.  The
off-diagonal ideal corners then link different quotient blocks, so the
direct-sum reduction used here is unavailable.  The argument does not
assert the maximum formula for arbitrary split AF extensions.
