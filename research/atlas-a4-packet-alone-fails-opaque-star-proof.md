---
rg: 2
id: atlas-a4-packet-alone-fails-opaque-star-proof
kind: route
title: Read opcode orders on the sixty exact packet alignments and compare regular spectra
target: atlas-a4-packet-alone-fails-opaque-star
requires:
  - atlas-shortest-a4-triangle-packet
artifacts:
  - experiments/atlas_a4_opaque_star_regular_screen.py
---

Work in the concrete chart `A8=GL_4(F2)`.  The exact screen reuses the
established enumeration of the thirty inner and thirty outer chart alignments
satisfying all thirty shortest `A4` pair-cubes.  For an alignment `alpha` and
one of

```text
T={t01,t12,t23,t30},
```

the relative opcode in `Reg(A8)` is the left-regular group unitary

```text
V_alpha(t)=lambda(alpha(t)t^-1).                       (1)
```

The screen computes the order of the group element in `(1)` by exact `F2`
matrix multiplication.  Among the inner alignments, the matrix

```text
00000100010000000001000000000001
```

satisfies every packet word and has the order profile

```text
(4,4,2,2).
```

This is not an isolated accident: twenty-two of the thirty inner alignments
and twenty of the thirty outer alignments have at least one leaf order
different from the hub order.  The script asserts both counts and the first
witness in each branch.

Use the two exact chart representations `lambda` and
`lambda o alpha=Ad(lambda(g)) o lambda` for the displayed inner alignment.
Every packet pair generates the required literal `A4`, so it defines the
corresponding context vertex representation.  The edge generators already
agree, hence every non-tree stable letter can be one.  Restriction of
`Reg(A8)` to any context `A4` is `1680 Reg(A4)`.  Therefore this is an exact
regular packet network with `eta=0`, proving `(A4-ORD-PROFILE)`.

It remains to compute the conjugacy gap.  In `Reg(A8)`, left multiplication by
an element of order `m` is a disjoint union of `|A8|/m` cycles of length `m`.
Hence an order-two opcode has spectral measure

```text
mu_2=(delta_1+delta_-1)/2,
```

while an order-four opcode has spectral measure

```text
mu_4=(delta_1+delta_i+delta_-1+delta_-i)/4.
```

The normalized Hoffman--Wielandt matching formula gives the minimum squared
Hilbert--Schmidt distance between their unitary orbits.  Match one quarter of
the mass at `1` and one quarter at `-1` at zero cost.  The remaining quarters
at `1` and `-1` must be matched to `i` and `-i`, each with squared chordal
cost two.  Thus

```text
inf_A ||T-A B A^*||_2^2=(1/4)2+(1/4)2=1.
```

The same calculation is unchanged after tensoring both opcodes by an identity
matrix.  Applying it to `t01,t12` versus the hub `t23` proves
`(A4-ORD-GAP)` and the claim.
