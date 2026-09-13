---
rg: 2
id: ha2-actions-give-fp2-twisted-brin-thompson-groups
kind: claim
title: A faithful action of type [HA_2] gives a simple twisted Brin–Thompson group of type FP_2 containing the actor
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that is the finite-presentation criterion for SV_G at type [A_2], where the actor must be finitely presented; this is the homological sufficient condition for FP_2 at type [HA_2], where the actor need only be of type FP_2 and so may fail to be recursively presented.
  abstract-btb-pairs-fp-and-relatively-simple: that records finite presentation of SV_G at type [A_2] together with relative simplicity; this records type FP_2 of SV_G at type [HA_2] and its consequence for FP_2 simple envelopes.
  type-a-action-gives-boone-higman-for-subgroups: that turns type (A) actions into finitely presented simple envelopes, which forces solvable word problem; this turns [HA_2] actions into FP_2 simple envelopes, which carry no computability restriction.
---

**ESTABLISHED (literature import)** by
`ha2-actions-give-fp2-twisted-brin-thompson-groups-citation`.

Let a group `G` act on a nonempty set `S`, and let `SV_G` be the (abstract)
twisted Brin–Thompson group of the action.

1. **Type `[HA_2]`.** The action is of type `[HA_2]` when `G` is of type `FP_2`,
   every point stabilizer is finitely generated, and `G` has finitely many
   orbits on `S × S`.
2. **`FP_2`.** If `G ↷ S` is of type `[HA_2]`, then `SV_G` is of type `FP_2`.
3. **Structure.** If `G` is finitely generated, `G ↷ S` has finitely many orbits
   of pairs and finitely generated point stabilizers, then `SV_G ≅ P/N` with
   `P` a free product of finitely many groups each commensurable to a finite
   direct power of `G`, and `N` finitely normally generated.
4. **Simplicity and embedding.** `SV_G` is relatively simple with largest normal
   subgroup the canonical kernel `SK_G = ker(SV_G → SV_{G/K})`, `K` the kernel
   of the action. For a faithful action `SK_G = 1`, so `SV_G` is simple. The map
   `ι_∅ : G → SV_G`, `g ↦ [·, id, g, ·]`, embeds `G`.

**Consequence.** If `G ↷ S` is faithful and of type `[HA_2]`, every subgroup of
`G` embeds in the simple group `SV_G` of type `FP_2`. This is the reduction
used by `every-countable-group-embeds-in-simple-fp2-via-ha2-actors`.
