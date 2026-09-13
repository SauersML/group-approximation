---
rg: 2
id: bernoulli-classes-meager-on-central-locally-finite-hosts
kind: claim
title: On groups with an infinite central locally finite residually finite subgroup of infinite index, every Bernoulli conjugacy class is meager in the closure of the Bernoulli classes
distinct_from:
  zero-rokhlin-supremum-forces-bernoulli-collapse: that is the open claim that zero Rokhlin supremum forces a collapse, whose Attempts propose a Baire-category argument; this proves that the category argument yields nothing on product hosts, because every Bernoulli class is meager there.
  semicontinuous-invariants-blind-above-rokhlin-supremum: that shows semicontinuous invariants cannot separate Bernoulli shifts above the supremum; this shows the complementary category tool cannot identify them on product hosts.
---

**ESTABLISHED (unreviewed)** by [[bernoulli-classes-meager-central-locally-finite-proof]].

Let `Γ` be a countable group and `P <= Γ` a subgroup that is infinite, central, locally finite and of infinite
index. Suppose `P` has finite-index subgroups `K_1 ⊇ K_2 ⊇ ...` with `∩_n K_n = {1}`. Let `A(Γ, X, µ)` be the
space of p.m.p. actions on a standard nonatomic space with the weak topology, and let `Y` be the closure of the
conjugacy class of a Bernoulli shift with nontrivial finite base. `Y` does not depend on the base
(`nontrivial-bernoulli-shifts-are-weakly-equivalent`).

**Theorem.** The actions in `Y` whose restriction to `P` has Kolmogorov–Sinai entropy `0` form a dense `G_δ`
subset of `Y`. Every Bernoulli shift with nontrivial base has positive entropy along `P`. So every Bernoulli
conjugacy class is meager in `Y`.

**Hosts.** `Γ = P × G` with `P = ⊕_(n>=1) Z/nZ`, `K_n = ⊕_(i>n) Z/iZ`, and `G` any countably infinite group.
These are the groups of Seward's Theorem 1.11 (arXiv:1501.03367v4), where `h^Rok_sup(P × G) = 0` as soon as
`h^Rok_sup(G) < ∞`.

**Reading for the negative direction.** By the topological 0-1 law, two non-meager Bernoulli classes in `Y`
would coincide. That is the category route recorded on `zero-rokhlin-supremum-forces-bernoulli-collapse`. On
product hosts it cannot start: every class is meager, and two meager classes can coincide only for reasons
category does not see.
- The approximants are generalized Bernoulli shifts over `Γ/K_n`. They are weakly contained in every Bernoulli
  shift, converge to it, and are deterministic along `P`.
- Simple hosts, such as the binary Leavitt units, Thompson's `V` and the tester host, have trivial center and are
  not covered.
- Over amenable `Γ` the theorem recovers the classical meagerness of Bernoulli classes, since there `Y` is the
  whole space and zero entropy is generic.
