---
rg: 2
id: simple-kazhdan-bernoulli-relation-hosts-contain-the-group
kind: claim
title: If the Bernoulli relation of an infinite simple Kazhdan group sits inside a free action's orbit relation, the acting group contains that group
distinct_from:
  free-action-containing-nonsofic-group-relation-is-nonsofic: that turns containment of a nonsofic group's free relation into nonsoficity of the host action; this shows that for Bernoulli actions of infinite simple Kazhdan groups such containment already forces a subgroup inclusion, so it reaches nothing beyond overgroups
  groups-containing-kun-thom-pair-have-nonsofic-actions: that constructs nonsofic actions of overgroups; this is a rigidity statement that limits which host actions can contain a Bernoulli relation
artifacts:
  - research/artifacts/solve-sofic-actions-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `H` be an infinite simple countable group with
property (T), and `β : H ↷ (Y,ν) = ([0,1]^H, Leb^(⊗H))` its Bernoulli shift. Let
`G ↷ (X,μ)` be an essentially free p.m.p. action of a countable group, `A ⊆ X`
measurable with `μ(A) > 0`, and `θ : (Y,ν) → (A,μ_A)` a measure-space
isomorphism with `θ(h·y) ∈ G·θ(y)` for every `h ∈ H` and a.e. `y`. Then there is
an injective homomorphism `ρ : H → G`, together with a measurable `ψ : Y → X`
satisfying `ψ(h·y) = ρ(h)·ψ(y)`.

The input is Popa's cocycle superrigidity for s-malleable actions of w-rigid
groups (arXiv:math/0512646; abstract verbatim in the artifact). The argument is
the standard one behind Popa's orbit equivalence superrigidity, specialized to
containment, with simplicity supplying injectivity. No novelty is claimed.
Proof: `simple-kazhdan-bernoulli-host-via-popa-superrigidity`.

**Consequence.** For a nonsofic `H` of this kind, the Bernoulli relation of `H`
fits inside a restricted orbit relation of a free action only for groups
containing `H`. Those groups are already nonsofic, so
`free-action-containing-nonsofic-group-relation-is-nonsofic` gains nothing from
malleable seeds of simple Kazhdan nonsofic groups
(`leavitt-unit-bernoulli-relations-have-no-sofic-host`).
