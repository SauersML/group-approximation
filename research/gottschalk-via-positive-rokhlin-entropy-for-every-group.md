---
rg: 2
id: gottschalk-via-positive-rokhlin-entropy-for-every-group
kind: route
title: Positive Rokhlin entropy over every group gives full Bernoulli Rokhlin entropy, hence surjunctivity
target: gottschalk-surjunctivity-conjecture
requires:
  - every-group-has-positive-rokhlin-entropy-action
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
---

Assume that every countably infinite group has a free ergodic p.m.p. action of
positive Rokhlin entropy. "Item n" refers to
`seward-per-group-rokhlin-entropy-of-bernoulli-shifts`.

**Countably infinite groups.** Fix a countably infinite group `G`.
- Applying item 3 to `P × G`, with `P = ⊕_n Z/nZ`, gives `h_sup(G) = ∞`, exactly
  as in step 1 of `bernoulli-classification-via-positive-rokhlin-entropy`.
- Item 1 then gives `h^Rok_G(k^G,u_k^G) = log k` for every `k`.
- Item 5, Seward's Corollary 4.1, gives Gottschalk's surjunctivity conjecture for
  `G`. It also gives Kaplansky direct finiteness for `G`.

**Independence from the host route.** `gottschalk-via-positive-rokhlin-entropy-host` reaches the same target through the tester host and the self-copy dichotomy `rokhlin-supremum-dichotomy-with-centralized-self-copies`. This route uses Seward's Theorem 1.11 on products `P × G` instead. The two routes share no intermediate claim.

**Finite groups.** They are surjunctive trivially, because an injective map from a
finite set to itself is onto.

**Scope.** This route needs the hypothesis for all groups, through the auxiliary
groups `P × G`. It claims no per-host form.

Cairn has no universal direct-finiteness root. That consequence is recorded here
and in item 5. The counterexample-side root
`leavitt-unit-group-algebra-not-directly-finite` would, once established, refute
the hypothesis.
