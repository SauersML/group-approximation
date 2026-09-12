---
rg: 2
id: boone-commutator-criterion-via-final-stable-letter
kind: route
title: Adjoin k over the normal closure of t and read membership as a commutator
target: boone-commutator-criterion-for-halting
requires: [boone-tower-good-subgroup-transport, boone-halting-subgroup-is-normal-closure, hnn-good-subgroup-lemma]
artifacts:
  - GroupApproximation/Computability/BooneGroupTower.lean
  - GroupApproximation/Computability/BooneGroupFreeBasis.lean
---

## Why sufficient

Form `(G'_M)' = HNNExtension G'_M A B id` with `A = B = <<t>>`.  For a single
stable letter with equal associated subgroups and the identity isomorphism,
Britton's Lemma applied to the length-one word `k^{-1} g k g^{-1}` gives

    [k, g] = 1   <->   g in <<t>>,

which is the one place the final letter is used and is the easiest Britton
application in the chain -- one stable letter, one syllable.

It remains to identify `<<t>>` with the halting condition on indices.  The
second prerequisite is `T'_M = <<t>>`, and the first is
`T_M = T'_M cap G`, so for a base-group element `t(a,b)`

    t(a,b) in <<t>>  <->  t(a,b) in T_M,

and `of_mem_basisSubgroup_iff` (from the sub-basis calculus, already
established) turns the right-hand side into `(a,b) in H_M`.  Chaining the two
biconditionals is the target.

The third prerequisite appears because the first two are statements *inside the
tower*: the identification `T_M = T'_M cap G` is an instance of the
good-subgroup lemma, and the same lemma is what licenses reading membership in
the last extension back down to the tower.

## Not a restatement of any prerequisite

None of the three mentions `k`, and none is a biconditional between a group
identity and a machine halting.  What this route adds is the final HNN
extension and the Britton argument for it; the prerequisites supply only what
`<<t>>` is.
