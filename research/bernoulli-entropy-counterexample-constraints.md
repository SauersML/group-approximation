---
rg: 2
id: bernoulli-entropy-counterexample-constraints
kind: claim
title: A Bernoulli isomorphism that changes base entropy forces a small Rokhlin supremum and passes to supergroups and finite-index subgroups
distinct_from:
  bernoulli-shift-entropy-classifies-for-every-group: that is the open universal classification; this proves necessary conditions on any single group where it fails.
  seward-per-group-rokhlin-entropy-of-bernoulli-shifts: that is Seward's imported computation of Bernoulli Rokhlin entropy; this derives from it, with co-induction and restriction, what a counterexample group must satisfy.
---

**ESTABLISHED.** Let `G` be a countably infinite group. Suppose `G ↷ (L^G,lambda^G)`
and `G ↷ (K^G,kappa^G)` are isomorphic with `h_1 = H(L,lambda) < h_2 = H(K,kappa)`,
and write `h_sup(G)` for Seward's Rokhlin supremum. Then:

(a) `G` is not sofic.

(b) `0 < h_1 < ∞` and `h_sup(G) ≤ h_1`. In particular, `2^G ≅ 3^G` forces
    `h_sup(G) ≤ log 2`, and INF(G) fails.

(c) If `h_2 = ∞`, then no free ergodic p.m.p. action of `G` has positive
    Rokhlin entropy.

(d) Every countable group containing `G` fails the classification with the same
    two bases. Every subgroup of finite index `k` in `G` fails it with bases of
    entropies `k·h_1 < k·h_2`.

(e) For every `t ∈ [0,∞)`, the Bernoulli shifts over `G` with base entropies
    `h_1 + t` and `h_2 + t` are isomorphic. So all base entropies
    `h_1 + n(h_2 − h_1)`, for `n ≥ 0`, give one isomorphism class.

Equivalently, from (d): the groups over which base entropy classifies Bernoulli
shifts form a class closed under infinite subgroups and under finite-index
supergroups. It contains every sofic group.

**Hosts.**
- No lower bound on `h_sup` is known for `L_(F_2)(1,2)^×` or for the Kun–Thom
  groups, so (a)–(e) exclude neither.
- `L^×` is simple and infinite, so the finite-index half of (d) is vacuous for it.
- The Kun–Thom groups are residually finite, but their finite-index subgroups are
  again nonsofic, so (d) gives no reduction to a sofic group.
