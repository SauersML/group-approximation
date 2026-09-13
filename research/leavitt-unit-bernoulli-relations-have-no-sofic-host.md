---
rg: 2
id: leavitt-unit-bernoulli-relations-have-no-sofic-host
kind: claim
title: No free p.m.p. action of a sofic group has a restricted orbit relation containing the Bernoulli relation of the binary Leavitt unit group
distinct_from:
  free-action-containing-nonsofic-group-relation-is-nonsofic: that is the general transfer from a contained nonsofic relation to the host action; this is the rigidity corollary saying the Bernoulli relation of one specific nonsofic group can never be contained in a sofic group's action
  openai-leavitt-unit-nonsofic: that is nonsoficity of the unit group itself; this is a statement about which orbit relations can contain its Bernoulli relation
artifacts:
  - research/artifacts/solve-sofic-actions-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `K = L_(F_2)(1,2)^×` be the binary Leavitt
unit group. For every countable sofic group `G`, every essentially free p.m.p.
action `G ↷ (X,μ)` and every measurable `A ⊆ X` with `μ(A) > 0`, there is no
measure-space isomorphism `θ : [0,1]^K → A` carrying the Bernoulli orbit
relation of `K` into `R_G|_A`.

So the containment route of
`free-action-containing-nonsofic-group-relation-is-nonsofic` cannot put a sofic
group outside Păunescu's class through Bernoulli actions of `K`. Any such seed
must be a free `K`-action that is not s-malleable, or a nonsofic group that is
not simple Kazhdan. Proof: `leavitt-unit-bernoulli-no-sofic-host-proof`.
