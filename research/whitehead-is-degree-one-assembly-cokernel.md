---
rg: 2
id: whitehead-is-degree-one-assembly-cokernel
kind: claim
title: The Whitehead group is the cokernel of the degree-one assembly map
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

For **every** group `G`, with no torsion hypothesis,

    Wh(G)  ==  coker( A_1^G : H_1(BG; K(Z)) -> K_1(ZG) ),

where `K(Z)` is the nonconnective algebraic `K`-theory spectrum of `Z` and
`A_1^G` is the degree-one component of the assembly
`BG_+ /\ K(Z) -> K(ZG)`.  Equivalently `Wh(G) = 0` iff `A_1^G` is onto.

The source of the map is completely known:

    H_1(BG; K(Z))  ==  C_2 (+) G_ab,

with `C_2 = K_1(Z) = {+-1}` hitting `[-1]` and `g` in `G_ab` hitting `[g]`.
So the sharpened form of the conjecture is: **no degree-one class of
`K_1(ZG)` exists beyond the scalar and loop classes.**  That is a far more
specific target than "show every invertible matrix is elementary".

Consequence: any theorem giving the regular-coefficient assembly isomorphism
`H_n(BG; K(Z)) -> K_n(ZG)` in degree one gives Whitehead vanishing, so the
`K`-theoretic Farrell--Jones conjecture implies
`whitehead-vanishing-torsion-free`.  The implication does not reverse:
degree-one surjectivity is not the higher-degree isomorphisms, the
coefficient versions, or the inheritance package that makes Farrell--Jones
usable under colimits and subgroups.

## Priority

**Folklore; claim no novelty.**  This is the trivial-family case of the
standard assembly picture and is the reason `Wh` is defined by that
quotient.  Lueck's survey states the conjecture (its 3.6) as a Farrell--Jones
statement but does not display this identity; the identity is nonetheless
standard.  It is noded because it converts the target into a statement about
a map whose source is computed, and because it is what connects this root to
`degree-one-assembly-surjective-torsion-free`, where the actual literature
progress lives.
