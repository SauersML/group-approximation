---
rg: 2
id: boone-halting-index-good-parameter-set
kind: claim
title: The base-group half of both good-subgroup verifications, as one parameter set
artifacts:
  - GroupApproximation/Computability/BooneGroupMachineIndex.lean
  - GroupApproximation/Computability/BooneGroupBase.lean
---

ESTABLISHED, for an arbitrary modular machine and with no HNN theory at all.
This is the paragraph of Simpson immediately after Definition 6:

> if `phi_i(t(a,b)) = t(a1,b1)` or `psi_j(t(a,b)) = t(a1,b1)`, then
> `(a,b) -> (a1,b1)`, hence `t(a,b) in T_M <-> (a,b) in H_M <-> (a1,b1) in H_M
> <-> t(a1,b1) in T_M`.  From this it follows that `T_M` is again a good
> subgroup of `G` with respect to `G'`.

Everything in it except the words "good subgroup" is index combinatorics plus
one machine fact, and all of that is proved:

* `Tsub_inf_Gsub_image` and `twSub_halting_inf_Gsub` compute
  `T cap G_{ab}^{MN}` and `T_M cap G_{ab}^{MN}`;
* `haltParams a b` -- the `(u,v)` for which the configuration
  `(a + uM, b + vM)` halts -- is shown to be *the same set* read through the
  source embedding and through the target embedding
  (`haltParams_eq_right`, `haltParams_eq_left`), which is the only place the
  machine enters, through
  [[modular-machine-halting-invariance]];
* `twSub_halting_inf_Gsub_src` versus `twSub_halting_inf_Gsub_right` /
  `_left` exhibit the source and target sides at a quadruple as the two images
  of that one parameter set.

That is the good-subgroup condition `phi(T_M cap G_{ab}^{MM}) = T_M cap
G_{c0}^{M^2,1}` with the associated isomorphism left implicit: the two sides
are images of one parameter set under the two embeddings, and `phi` is
`emb c 0 M^2 1` after `(emb a b M M)^{-1}`.

## What is deliberately left out

Supplying the isomorphism -- rewriting these two images along that composite
inside the tower -- is [[boone-tower-good-subgroup-transport]], and it is open.
Keeping it out is what lets this claim be proved with no HNN theory, so that
the only genuinely hard step of the chain, [[hnn-good-subgroup-lemma]], stands
alone.
