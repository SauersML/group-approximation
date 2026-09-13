---
rg: 2
id: nonamenable-bernoulli-shifts-are-weakly-isomorphic
kind: claim
title: Over every countable nonamenable group, any two nontrivial Bernoulli shifts factor onto each other
distinct_from:
  nontrivial-bernoulli-shifts-are-weakly-equivalent: that is weak equivalence in Kechris's sense, from Abért–Weiss, which concerns finite-window statistics; this is weak isomorphism, factor maps in both directions, and it needs nonamenability.
---

**ESTABLISHED (import)** by [[nonamenable-bernoulli-shifts-are-weakly-isomorphic-citation]].

Let `G` be a countable nonamenable group and let `(K, κ)` and `(L, λ)` be nontrivial standard probability
spaces. Then there is a `G`-equivariant measurable map `Φ : K^G → L^G` with `Φ_* κ^G = λ^G`, and one in the
other direction.

**Reading.**
- Base entropy can increase under factor maps. A Bernoulli shift of arbitrarily small base entropy factors
  onto every other. The Ornstein–Weiss map from the 2-shift onto the 4-shift over `F_2` is the first example.
- Over amenable groups this is false, because Kolmogorov–Sinai entropy does not increase under factor maps.
- Use on main: `iid-generators-not-dense-at-positive-rokhlin-supremum` places i.i.d. partitions of every
  distribution inside a Bernoulli factor of small base entropy.
