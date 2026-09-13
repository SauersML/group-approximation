---
rg: 2
id: sofic-actions-restrict-to-co-amenable-subgroups
kind: claim
title: An action is sofic as soon as its restriction to some co-amenable subgroup is sofic
distinct_from:
  co-amenable-induction-of-sofic-actions: that treats a transitive amenable action and its point stabilizer; this allows any co-amenable subgroup and any action, including non-transitive and non-amenable ones.
  separating-sofic-quotient-sets-make-an-action-sofic: that pulls labels back along global equivariant maps and multiplies actions; this transfers soficity from a co-amenable subgroup's restriction and adds a local version of separation with partial maps.
  uas-base-gives-sofic-hnn-coset-action: that uses strongly co-amenable coset actions, which factor through amenable quotients; this concerns restrictions to co-amenable subgroups, which need not factor through anything.
artifacts:
  - research/artifacts/pfg-positive-co-amenable-restriction-2026-09-13.md
---

ESTABLISHED (unreviewed). Soficity is GKP Definition 2.1(5).

**(CA) Co-amenable restriction.** Let `G` be countable, `H ≤ G` co-amenable,
and `α : G ↷ X` an action on a countable set. If `α|_H` is sofic, then `α` is
sofic. With GKP Proposition 2.15(3) this becomes: `α` is sofic iff `α|_H` is
sofic.

**(FI) Finite-index induction.** If `H ≤ G` has finite index and `H ↷ Y` is
sofic, then `G ↷ G ×_H Y` is sofic.

**(LS) Local separation.** Suppose that for all finite `F ⊆ G` and `E ⊆ X`
there are a sofic `G`-set `Y` and an injective `ι : E → Y` that is
`F`-equivariant wherever defined. Then `α` is sofic.

**(G) Groups.** A group with a co-amenable sofic subgroup is sofic.

Special cases of (CA):

- `H = {1}` recovers GKP Theorem 2.17 (every action of an amenable group is
  sofic).
- A point stabilizer of a transitive amenable action gives the `⇐` half of
  [[co-amenable-induction-of-sofic-actions]].

(LS) contains (S1) of [[separating-sofic-quotient-sets-make-an-action-sofic]].
It also contains the subgroup-approximation step of
`GroupApproximation/Sofic/SoficActionChabauty.lean` (dossier Proposition 30.3).

The proof of (CA) takes a Følner set `Φ` of `G/H` and a model `ψ` of `α|_H`,
and uses `Φ × A_H` with the section cocycle
`c(g,y) = σ(gy)^-1 g σ(y)` and labels `π_(y,a)(x) = π^H_a(σ(y)^-1 x)`.

DERIVATION [[sofic-actions-restrict-to-co-amenable-subgroups-proof]].

Novelty was checked only against GKP Section 2 and the graph's own nodes. (G)
in the non-normal case is probably in the literature.
