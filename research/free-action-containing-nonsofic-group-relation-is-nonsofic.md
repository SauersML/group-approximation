---
rg: 2
id: free-action-containing-nonsofic-group-relation-is-nonsofic
kind: claim
title: A free p.m.p. action whose orbit relation contains the relation of a free action of a nonsofic group is not sofic
distinct_from:
  groups-containing-kun-thom-pair-have-nonsofic-actions: that transfers nonsoficity to groups containing a Kun--Thom pair, by co-induction through a genuine subgroup; this transfers it to any free action whose restricted orbit relation contains a free action of a nonsofic group, with no subgroup inclusion assumed
  paunescu-class-is-measure-equivalence-invariant: that moves membership in Paunescu's class along couplings of finite covolume on both sides; this is a one-sided containment statement about a single action
artifacts:
  - research/artifacts/solve-sofic-actions-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `G ↷ (X,μ)` be an essentially free p.m.p.
action of a countable group, let `A ⊆ X` be measurable with `μ(A) > 0`, and let
`H ↷ (A,μ_A)` be an essentially free p.m.p. action of a countable group `H`
(`μ_A` the normalized restriction) whose orbit relation `R_H` is contained in
the restriction `R_G|_A`. If `H` is not sofic, then `G ↷ X` is not sofic
(Păunescu Definition 1.4), so `G` lies outside Păunescu's class `𝒮`.

Every ingredient is a definition-level permanence: Păunescu Proposition 1.15,
Cordeiro Proposition 3.2(a), and restriction of a sofic embedding to a
subrelation. No novelty is claimed. Proof: `nonsofic-subrelation-transfer-proof`.

**Use.** A nonsofic seed for a sofic group `G` does not need a subgroup of `G`.
It is enough that one free action of a nonsofic group lives inside a restricted
orbit relation of some free `G`-action. Nonsofic groups exist
(`finitely-presented-nonsofic-group-exists`), so this is a live source of seeds.
`simple-kazhdan-bernoulli-relation-hosts-contain-the-group` shows that the
malleable actions of the known nonsofic Kazhdan witness cannot be used this way
for a sofic host.
