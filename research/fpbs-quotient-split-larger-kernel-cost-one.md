---
rg: 2
id: fpbs-quotient-split-larger-kernel-cost-one
kind: claim
title: A free action factoring onto a free finite-cost action of an infinite quotient by any normal overgroup of a bounded-cost normal subgroup has cost one
distinct_from:
  fpbs-quotient-split-actions-have-cost-one: that requires the factor action to be a free action of G/N itself; this allows the kernel M of the factor action to be any normal subgroup containing N of infinite index, with M/N possibly infinite and M of unbounded cost, which is what profinite boundary actions need when N is not closed in the chain topology.
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that asserts cost one for every free action of G; this proves it only for actions with a free finite-cost factor of some infinite quotient G/M with N contained in M.
artifacts:
  - research/artifacts/fpbs/normal-finite-cost-rank-gradient-2026-09-17.md
---

**Theorem A'.** Assume:

* `N ◁ G` is infinite, and every free p.m.p. action of `N` has cost at most `K < ∞`;
* `M ◁ G` contains `N` and has infinite index;
* `alpha` is a free p.m.p. action of `G`;
* `alpha` has a `G`-equivariant factor onto an essentially free p.m.p. action `sigma` of `G/M`, with `M` acting trivially and `C(sigma) < ∞`.

Then `C(alpha) = 1`.

**Proof.** Section 2 of the linked note: pay the `N`-cost on the sparse `M`-invariant set `phi^{-1}(A)`. Close up to `R_M` with normalizing lifts of generators of `M/N`, placed on small complete sections of `R_N` (Lemma 2.1). Lift a graphing of `R_sigma|A` at small complete sections of `R_N`. Fibres of `phi` within an orbit are single `M`-orbits (Lemma 2.2).
