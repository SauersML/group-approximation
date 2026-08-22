---
rg: 2
id: atlas-q1920-agl5-seam-proof
kind: route
title: Realize the characteristic module regularly and exhaust its full affine normalizer
target: atlas-q1920-agl5-has-no-collision-involution
requires:
  - atlas-q1920-is-radial-holonomy-extension
artifacts:
  - experiments/atlas_a4_q1920_agl5_seam.g
  - research/artifacts/atlas-a4-q1920-agl5-seam.json
---

For each marking, exact complement enumeration gives 64 `A5` complements
to `V`, two of which contain the marked radial `A`.  Acting on the 32 right
cosets of such a complement makes `V` a regular elementary abelian
permutation group.

GAP computes its full normalizer in `Sym(32)`, verifies `(AGL5-1)`, and then
computes the pointwise centralizer of the marked `A`.  The centralizer has
only twelve elements, so evaluating the two literal collision words on all
seven involutions is an exhaustive calculation, not a random target search.
Both marked computations give zero solutions.

For the abstract consequence, if `V normal L` and `C_L(V)=V`, conjugation
induces an injection `L/V -> Aut(V)`.  The resulting extension embeds into
`V semidirect Aut(V)=Hol(V)`, so the exact affine calculation applies.
