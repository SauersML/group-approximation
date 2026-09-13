---
rg: 2
id: rigid-actions-have-no-dbar-close-bernoulli-models
kind: claim
title: Shift models of a rigid action stay at d-bar distance at least half the collision complement from every Bernoulli measure, over every group
distinct_from:
  rokhlin-entropy-is-the-bernoulli-approximation-threshold: that proves weak* approximation of a Bernoulli measure by shift models of any free ergodic action of small Rokhlin entropy; this proves that for rigid actions those models never approach it in the d-bar metric.
  iid-generators-dense-at-zero-rokhlin-supremum: that asks for density of generating i.i.d. partitions inside one Bernoulli shift; this is a lower bound on the joining distance between models of rigid actions and i.i.d. processes.
---

**ESTABLISHED (unreviewed)** by [[rigid-actions-have-no-dbar-close-bernoulli-models-proof]].

Let `G` be a countably infinite group and `G ↷ (X, μ)` a p.m.p. action. Call it **rigid** if there are
`g_n ∈ G` leaving every finite set with `μ(g_n A Δ A) → 0` for every measurable `A`. For a finite set `L`
and `G`-invariant probability measures `ν, ν'` on `L^G`, put

    d̄(ν, ν') = inf { J((x, y) : x(1_G) ≠ y(1_G)) : J a G-invariant joining of ν and ν' },

and for a probability vector `λ` on `L` put `c_λ = 1 − Σ_l λ(l)^2`, the probability that two independent
`λ`-labels differ.

**Theorem.** Let `α: X → L` be measurable and `ν` the law of `x ↦ (g ↦ α(g^-1 x))`. If `X` is rigid, then
`d̄(ν, λ^G) ≥ c_λ / 2` for every probability vector `λ` on `L`.

No freeness, ergodicity or generation is assumed. In particular every shift model of a rigid free ergodic
action, in the sense of `rokhlin-entropy-is-the-bernoulli-approximation-threshold`, stays at `d̄`-distance
`≥ c_λ/2` from `λ^G`.

**Hosts with rigid free ergodic actions.** Every infinite maximally almost periodic group, in particular
every infinite residually finite group, has one: left translation on the closure `K` of `G` in a compact
group containing it injectively (for instance a profinite completion), with Haar measure. This covers the
Kun–Thom groups (residually finite, per `bernoulli-entropy-counterexample-constraints`) and products `P × G`
with `P = ⊕_n Z/nZ` and `G` residually finite. The binary Leavitt unit group, Thompson's `V` and the tester
host are simple and not covered; whether they have rigid free ergodic actions is not recorded here.

**Reading.**
- Over a group with Rokhlin supremum `0`, rigid free ergodic actions have Rokhlin entropy `0`, so their
  shift models converge weak* to every `λ^G`. The theorem shows that this convergence never improves to `d̄`.
  So `d̄` is not weak*-continuous at `λ^G` on such a group, among essentially free measures of Rokhlin
  entropy `0`. The consequence for finitely determined measures is posed as
  `bernoulli-measures-not-finitely-determined-at-zero-supremum`.
- A route to `zero-rokhlin-supremum-forces-bernoulli-collapse` through finitely determined properties must
  therefore restrict the class of measures it compares, for example to models of mixing actions. Models of
  another Bernoulli shift are not excluded by the theorem.
