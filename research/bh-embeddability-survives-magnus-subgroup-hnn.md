---
rg: 2
id: bh-embeddability-survives-magnus-subgroup-hnn
kind: claim
title: Magnus-subgroup HNN extensions of one-relator groups with finitely presented simple envelopes have finitely presented simple envelopes
distinct_from:
  bh-embeddability-survives-decidable-edge-hnn: that allows any finitely generated base and any finitely generated associated subgroups with decidable membership; this is the special case where the base is a one-relator group and the associated subgroups are Magnus subgroups matched by a bijection of their bases, which is all the Magnus--Moldavanskii induction consumes.
  bh-embeddability-forces-decidable-edge-membership: that shows decidable edge membership is necessary for such a permanence and that the unrestricted closure fails; this asserts the closure for Magnus edges, whose membership is decidable by Magnus.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that settles the graphs of groups whose edge groups have finite index in the vertex groups; Magnus edges have finite index only over free bases.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

Let `H = <Y | s>` be a one-relator group, with `Y` finite and `s` cyclically
reduced and nontrivial, that embeds in a finitely presented simple group. Let
`Y_1, Y_2 ⊆ Y` each omit some letter occurring in `s`, and let
`β : Y_1 -> Y_2` be a bijection. By the Freiheitssatz (item 1 of
`magnus-moldavanskii-hierarchy-with-decidable-edges`), `β` extends to an
isomorphism `<Y_1> -> <Y_2>`. Then the HNN extension

    H*_β = <H, t | t y t^-1 = β(y)  (y ∈ Y_1)>

embeds in a finitely presented simple group.

**OPEN.**

## Relation to the one-relator problem

- **Sufficient.** By `magnus-hnn-permanence-forces-one-relator-boone-higman`,
  this claim implies `one-relator-groups-satisfy-boone-higman`.
- **Equivalent on the data the induction uses.** The induction uses only shift
  data: `Y` is a union of index chains `y_m, ..., y_M` whose end letters occur in
  `s`, `Y_1` drops the top of each chain, `Y_2` drops the bottom, and `β` raises
  the index. For shift data, `H*_β` is itself a one-relator group, by the Tietze
  moves in the proof route. So on shift data this claim is equivalent to the
  one-relator problem. The gain from the reformulation is the extra hypothesis:
  one may assume the base `H` already embeds.
- **Consequence of the general premise.** It follows from
  `bh-embeddability-survives-decidable-edge-hnn` by
  `magnus-hnn-permanence-from-decidable-edge-permanence`.

## Attempts

1. **General decidable-edge permanence.** Wired as
   `magnus-hnn-permanence-from-decidable-edge-permanence`. *Deferred* to that
   premise.
2. **Rigid permutation groups of the Bass--Serre tree** (Bux--Llosa Isenrich--Wu).
   Their finiteness argument needs a locally finite tree, i.e. associated
   subgroups of finite index in `H`. Two free subgroups of equal rank with
   finite index make the torsion-free group `H` virtually free, hence free. So
   this reaches only free bases. *Dies* for non-free bases.
   - **Bigger hosts do not help.** One cannot embed the HNN extension in a
     larger locally finite tree host instead: for the Baumslag--Gersten step
     (`H = BS(1,2)`, edges `<a_0>`, `<a_1>`), the base is elliptic in every tree
     action (`baumslag-gersten-base-is-elliptic-in-every-tree-action`). Any host
     tree must have vertex stabilizers containing a `BS(1,m)`, which excludes
     the free, abelian and nilpotent `BS_G` families of that paper.
3. **Twisted Brin--Thompson group of the tree action.** The vertex set carries
   infinitely many orbits of pairs, since distance is an invariant. This is
   attempt 1 of `bh-embeddability-survives-decidable-edge-hnn`, and it applies
   verbatim. *Dies* for this action.
4. **Hyperbolic combination.** Magnus subgroups are cyclonormal: `H ∩ gHg^-1` is
   cyclic for `g ∉ H` (Bagherzadeh 1976, as reported in the Linton--Nyberg-Brodda
   survey). They are malnormal with torsion (B. B. Newman). A malnormal
   quasi-convex combination keeps hyperbolicity, but by Linton's Theorem 7.1
   no hierarchy of a group containing a Baumslag--Solitar subgroup is
   quasi-convex with hyperbolic top group. *Dies* for such groups.
