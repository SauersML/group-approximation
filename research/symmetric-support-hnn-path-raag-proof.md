---
rg: 2
id: symmetric-support-hnn-path-raag-proof
kind: route
title: Identify the height kernel with a path right-angled Artin group
target: symmetric-free-support-hnn-remains-hyperlinear
requires:
  - free-phase-context-support-is-a-proper-free-factor
  - ascending-hnn-cannot-create-nonhyperlinearity
---

Eliminate `L_1` from `(SFH1)`.  The base relation
`[L_0,L_1]=1` becomes `[L_0,tL_0t^(-1)]=1`.  Conjugating by powers of `t`
gives `(SFH2)`.  Britton normal form supplies no relations among the
conjugates beyond the internal relations of each `L_n` and these adjacent
commutations.  Hence the height kernel is their graph product over the
bi-infinite path.

Present `L` as the right-angled Artin group of a finite graph `Lambda`.  The
graph product over a finite path is the right-angled Artin group obtained by
placing one copy of `Lambda` at every site and adding all edges between every
pair of vertices at neighboring sites.  It is residually finite.  Every
finite subset of the full height kernel lies in one such finite-interval
group, proving hyperlinearity of the directed union.  The quotient of
`(SFH1)` by the height kernel is infinite cyclic; the extension-permanence
theorem used in
`ascending-hnn-cannot-create-nonhyperlinearity` finishes the proof.

If a factor `G_0` is fixed by the HNN isomorphism, the stable letter commutes
with it and the presentation splits as `G_0 times E`.  Direct products of
hyperlinear groups are hyperlinear.
