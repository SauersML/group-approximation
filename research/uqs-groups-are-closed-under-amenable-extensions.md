---
rg: 2
id: uqs-groups-are-closed-under-amenable-extensions
kind: claim
title: An extension of a uniformly quantitatively surjunctive group by an amenable group is uniformly quantitatively surjunctive
distinct_from:
  amenable-extensions-of-uqs-groups-are-surjunctive: that concludes only surjunctivity of the extension, which cannot be iterated; this keeps the uniform deficit with an explicit constant, so towers of amenable extensions stay UQS.
  surjunctive-groups-are-uniformly-quantitatively-surjunctive: that is the open statement that every surjunctive group is UQS; this is permanence of UQS along extensions with amenable quotient and adds no new host by itself.
  maximal-bernoulli-rokhlin-entropy-makes-groups-uqs: that produces UQS from maximal Bernoulli Rokhlin entropy; this propagates UQS from a normal subgroup to the whole group.
artifacts:
  - research/artifacts/gk3-approx-surjunctive-2026-09-14.md
---

**ESTABLISHED** by `uqs-amenable-extension-closure-proof`. Not yet independently re-derived.

UQS is the property of `amenable-extensions-of-uqs-groups-are-surjunctive`: for every finite alphabet `B` and
`w >= 1` there is `delta(B,w) > 0` such that no injective automaton maps `(B^n x D^j)^N` into
`(Y_1 x ... x Y_n) x (D^(j'))^N` when `(j' - j) log|D| < delta(B,w) n` and each `Y_i <= B^N` is a subshift missing
some pattern on at most `w` sites.

**Theorem.** Let `N` be a normal subgroup of `G` with `G/N` amenable. If `N` is UQS with constant function
`delta_N`, then `G` is UQS with

```text
delta_G(B, w) = min_(1 <= u <= w) delta_N(B^u, w) / (4 w^3).
```

**Corollaries** (artifact Section 3.3).
- **Towers.** If `N = G_0 <| G_1 <| ... <| G_k = G` with every `G_(i+1)/G_i` amenable and `N` UQS, then `G` is UQS,
  hence surjunctive. Part 1 of `amenable-extensions-of-uqs-groups-are-surjunctive` is the one-step
  surjunctivity case.
- **Calibration.** The trivial group is UQS with `delta(C, w) = log(|C| / (|C| - 1))`. So every amenable group is
  UQS with `delta(B, w) = -log(1 - |B|^(-w)) / (4 w^3)`.
- **Products.** `N x Q` is UQS for every UQS `N` and amenable `Q`.

**Scope** (artifact Section 3.4).
- **No new host.** No nonsofic group is known to be UQS. The theorem says only that one such group would make every
  group in its amenable-extension towers UQS and surjunctive.
- **AQS.** The asymptotic version does not propagate by this device, because the transplanted margin grows with the
  Følner set.
- **Known witnesses.** `G x W` and `G x D`, for surjunctive `G` and Kun--Thom wreaths `W` or doubles `D`, are already
  surjunctive by `products-with-lef-permanence-closure-factors-are-surjunctive`.

Proof: route `uqs-amenable-extension-closure-proof`, artifact Section 3.2.
