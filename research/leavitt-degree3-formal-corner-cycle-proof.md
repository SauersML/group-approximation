---
rg: 2
id: leavitt-degree3-formal-corner-cycle-proof
kind: route
title: Enumerate sign topologies and compare formal free-word corners
target: leavitt-degree3-formal-corner-cycle-is-absent
requires:
  - leavitt-two-relator-corner-peeling
---

There are `C(11,4)=330` length-eleven sign words of exponent sum three.
Computing the three cyclic-cover orbits leaves exactly eleven whose valences
are `(1,1,9)`.  In every case the nine-valent corner sizes are eight
singletons and one triple.

For each topology the artifact next chooses the four identity slots in all
`C(11,4)=330` ways and labels the remaining slots by distinct free symbols.
Words are stored as tuples `(coefficient-copy, slot)`, so tuple equality is
exact free-product normal-form equality.  It compares both orientations of
both unary words with every nonempty target corner.  The exhaustive output is

```text
topologies 11
identity_layouts 3630
target_shapes {(1, 1, 1, 1, 1, 1, 1, 1, 3): 11}
literal_minimal_four_incidence_cycles 0
```

Thus the minimal joint incidence is absent at the formal topology level.
