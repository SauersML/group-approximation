---
rg: 2
id: bowen-every-countably-infinite-group-is-almost-ornstein
kind: claim
title: Over every countably infinite group, Bernoulli shifts over equal-entropy bases that are not two-atom spaces are isomorphic
distinct_from:
  bernoulli-shift-entropy-classifies-for-every-group: that asks whether base entropy classifies all Bernoulli shifts over every group, two-atom bases included; this imports Bowen's theorem, which settles every case except two-atom bases.
  seward-small-support-relative-generators: that imports Seward's generator theorem, which realises prescribed distributions strictly above Rokhlin entropy; this imports an isomorphism theorem, which realises distributions of exactly equal Shannon entropy.
---

**ESTABLISHED (import)** by [[bowen-every-countably-infinite-group-is-almost-ornstein-citation]].

Let `G` be a countably infinite group and `(K, κ)`, `(L, λ)` standard probability spaces, neither
supported on two atoms, with `H(κ) = H(λ)`. Then `G ↷ (K^G, κ^G)` and `G ↷ (L^G, λ^G)` are measure
conjugate.

**Use.** If `B(p)` is the Bernoulli shift with base `p` and `q` has `H(q) = H(p)` (both with at least
three atoms), then the time-zero partition of `B(q)`, pushed through the isomorphism, is a
generating partition of `B(p)` with distribution `q`. See
[[distribution-certificates-are-shannon-monotone]].
