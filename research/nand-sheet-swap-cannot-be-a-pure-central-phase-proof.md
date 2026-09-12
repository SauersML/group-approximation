---
rg: 2
id: nand-sheet-swap-cannot-be-a-pure-central-phase-proof
kind: route
title: Evaluate the swapped sign on the three NAND atoms
target: nand-sheet-swap-cannot-be-a-pure-central-phase
requires:
  - s4-nand-cycle-holonomy-is-one-s2-bit
---

On `e_(+,+)`, the sign `R` is `+1`, and the swap carries that atom to
`e_(+,-)`, where `R=-1`; hence `HRH^*=-1` on the first atom.  The same
calculation gives `+1` on the second atom.  The third atom is preserved and
has `R=+1`.  Therefore `HRH^*` has the diagonal values

```text
(-,+,+).                                                (NSP1)
```

The word `-SR` has exactly these values on the three supported sign pairs,
proving `(NSS2)`.

For the pure-phase obstruction, restrict `(NSS3)` to `e_(-,+)`.  The left
side is `+e_(-,+)` because that atom is preserved and `R=+1` there.  The
right side is `-e_(-,+)`.  Thus `(NSS3)` implies
`2e_(-,+)=0`, so the third atom vanishes over `C`.  This proves that a pure
central minus is incompatible with the full NAND support.

The matrices `(NSS4)` directly give `(NSP1)` and satisfy `(NSS2)`.  Diagonal
signs together with all coordinate permutations generate the stated finite
signed permutation group and span all matrix units in the defining block,
so this is an exact irreducible finite group-corner realization.  Finally
centrality and involutivity of `J,S` give `(JS)^2=q`, proving `(NSS5)`.
