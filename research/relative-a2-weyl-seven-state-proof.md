---
rg: 2
id: relative-a2-weyl-seven-state-proof
kind: route
title: Cycle the second packet through two fresh reservoirs along the A2 braid
target: relative-a2-weyl-orbit-has-seven-state-gauge-model
requires:
  - mixed-cross-zero-squares-have-four-state-gauge-model
  - adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
---

On root indices, the product of adjacent transpositions `(1 2)(2 3)` is a
three-cycle (up to the harmless orientation convention).  Conjugation by
its permutation-Weyl lift gives the three roots in `(RAW1)`, and the Coxeter
braid gives `H^3=1`.  Conjugating by `U_0` proves `(RAW2)`.

The projections in `(RAW3)` are diagonal, commute, have rank two, and obey

```text
P_0+P_1-2P_0P_1=P_A.                                  (1)
```

The two disjoint three-cycles in `(RAW4)` send the ordered basis pairs
`(e_2,e_3)` first to `(e_4,e_6)` and then to `(e_5,e_7)`, proving
`(RAW5)`.  Both target pairs are disjoint from `(e_1,e_2)`, while the source
pairs meet in `e_2`, proving `(RAW6)`.

For a base-packet occurrence `g`, use the controlled unitary

```text
g[P]=(1-P) tensor 1+P tensor g.
```

If `N` is the fixed native label implementer of `(RAW1)`, then

```text
(G tensor N) g[P_1] (G tensor N)^(-1)
```

is the correct next root-position occurrence controlled by `GP_1G^*`.
Iterating twice gives the second line of `(RAW5)`, and the third iterate
returns exactly because `G^3=N^3=1`.  This verifies the full relative
occurrence orbit and its braid/order law.

At each of the two nontrivial stages, the branch-one carrier is orthogonal
to `P_0`; hence every composable positive-root pair and its opposite-factor
mixed square act on orthogonal carrier summands.  Both crossed-zero words
are therefore exact.  Equation `(1)` and the involution calculation from
the four-state model verify the source fold and reverse-product Whitehead
relation.  The parent packet is active on the nonzero space `P_AH_0`, so the
mark survives with all displayed defects zero.
