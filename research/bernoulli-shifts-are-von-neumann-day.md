---
rg: 2
id: bernoulli-shifts-are-von-neumann-day
kind: claim
title: Every nontrivial Bernoulli shift of a nonamenable group carries an essentially free ergodic action of the rank two free group whose orbits lie inside the group's orbits
distinct_from:
  nonamenable-bernoulli-shifts-are-weakly-isomorphic: that imports Bowen's Corollary 1.3, that nontrivial Bernoulli shifts factor onto each other; this imports Theorem 1.1 of the same paper, a measurable free subgroup inside every nontrivial Bernoulli shift, from which that corollary is derived.
---

**ESTABLISHED (import)** by [[bernoulli-shifts-are-von-neumann-day-citation]].

Let `Γ` be a countable nonamenable group and `(K, κ)` a nontrivial probability space. Then there is an essentially
free, ergodic action of `F_2` on `(K^Γ, κ^Γ)` such that, off a null set, each `F_2`-orbit is contained in a
`Γ`-orbit.

**Remarks (derived here, not part of the import).**
- *Generators preserve measure.* Each generator `T` of such an action is a Borel bijection whose graph lies in the
  orbit relation of the measure-preserving `Γ`-action. So `T(x) = c(x)·x` for a Borel `c: K^Γ → Γ`, by Lusin–Novikov
  uniformization, and `c` is unique off the null set where `Γ` does not act freely.
- *Why.* On the pieces `{c = g}`, `T` is the translation by `g`, and it is injective. So
  `κ^Γ(T B) = Σ_g κ^Γ(g(B ∩ {c = g})) = κ^Γ(B)` for every Borel `B`.
- *Consumer.* `spectral-gap-refutes-exactification-on-nonamenable-groups` runs the Ornstein–Weiss map along such an
  action.
