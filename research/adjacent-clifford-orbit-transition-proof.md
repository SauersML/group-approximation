---
rg: 2
id: adjacent-clifford-orbit-transition-proof
kind: route
title: Count root-coordinate eigenspaces in the four Clifford orbits
target: adjacent-clifford-orbit-transition-graph
requires:
  - fixed-clifford-sectors-have-zero-adjacent-opposite-overlap
  - iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree
---

Let `pi` be an irreducible level-`a` representation whose restriction to
the newest normal abelian layer `L_a` has Clifford orbit `O`. Clifford
theory gives

```text
pi|_(L_a)=m directSum_(mu in O) mu                       (CTP1)
```

for one multiplicity `m`; hence every character eigenspace has physical
dimension `dim(pi)/|O|`.

The pullback calculation of
`fixed-clifford-adjacent-overlap-proof` applies to every `mu`, not only
`(1,1,1)`. If the opposite newest-layer element is
`1+2^aX(A,B,C)`, its upper level-`a` reduction is
`1+2^(a-1)X(0,B,0)`. On the `mu=(alpha,beta,gamma)` eigenspace it acts by

```text
(-1)^(beta B).                                          (CTP2)
```

Thus a `beta=0` eigenspace can overlap only a target with zero newest-layer
character, while a `beta=1` eigenspace forces target character
`(0,1,0)`, whose `G_(a+1)` orbit is `O_B`. Counting `beta=0,1` in `(COT1)`
gives

```text
             O_0  O_F  O_A  O_B
beta=0:       1    0    2    1
beta=1:       0    1    1    2,                         (CTP3)
```

and `(CTP1)` turns these counts into the weights `(COT2)`.

These are not merely exclusions. Each relevant character block is stable
under the abstract Iwahori (characters with a fixed `beta` form unions of
orbits under its mod-two stabilizer), and any irreducible Iwahori
constituent in such a block occurs in the restriction of some target vertex
irreducible by Frobenius reciprocity. Its target newest-layer orbit is the
one forced by `(CTP2)`. Hence `(COT2)` is the exact support graph and the
displayed numbers are its sharp aggregate source capacities; no assertion
is made that all capacities can be saturated simultaneously with prescribed
target marginals.

For the reverse orientation, an upper newest-layer element
`1+2^aX(A,B,C)` pulls back in the depth-`a` opposite chart to
`1+2^(a-1)X(0,0,C)`. Formula `(CTP2)` becomes `(-1)^(gamma C)`.
The `gamma=1` counts in the four orbits are again `0,1,1,2`, proving the
same directed graph.

Finally the orbit sizes in `(COT1)` are `1,1,3,3`; orbit--stabilizer gives
`(COT3)`. Iterating the only nonzero recurrent arrow multiplies available
source capacity by at most `2/3` at each step, which proves the last
assertion of the claim.

