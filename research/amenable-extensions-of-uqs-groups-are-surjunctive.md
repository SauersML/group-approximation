---
rg: 2
id: amenable-extensions-of-uqs-groups-are-surjunctive
kind: claim
title: Extensions of uniformly quantitatively surjunctive groups by amenable groups are surjunctive
distinct_from:
  products-with-a-sofic-factor-are-surjunctive: that transplants along sofic models of a direct factor; this transplants along Følner sets of an amenable quotient, twisted extensions included, and needs the deficit to be uniform over tracks missing different patterns.
  normal-surjunctive-decoder-memory-forces-surjectivity: that is the boundary-free case, needing only surjunctivity of the kernel; this handles decoders reading across cosets, where the boundary loss must be paid by a quantitative deficit.
  sofic-kernel-amenable-quotient-permanence: that is permanence of soficity; this is permanence of surjunctivity for nonsofic kernels satisfying a deficit property.
artifacts:
  - research/artifacts/amenable-extension-surjunctivity-transfer-2026-09-12.md
---

**ESTABLISHED** by `amenable-extensions-of-uqs-groups-proof`.

A group `N` is *uniformly quantitatively surjunctive* (UQS) if for every finite `B` and `w >= 1` there is `delta(B,w) > 0`
such that no injective automaton maps `(B^n x D^j)^N` into `(Y_1 x ... x Y_n) x (D^(j'))^N` whenever
`(j' - j) log|D| < delta n` and each `Y_i <= B^N` is a subshift missing a pattern on at most `w` sites. `N` is
*asymptotically quantitatively surjunctive* (AQS) if for each `B`, `w` and `K` such maps are excluded for all large `n`
once `(j' - j) log|D| <= K`.

**Theorem.** Let `N` be a normal subgroup of `G` with amenable quotient.
1. If `N` is UQS, then `G` is surjunctive.
2. If `N` is AQS and `G/N` is two-ended, then `G` is surjunctive.

**Heredity.** UQS and AQS pass to subgroups and directed unions, with the same constants.

**Corollary.** If `N` is AQS, every ascending HNN extension `N *_phi` is surjunctive.

**Scope.**
- **No new unconditional groups.** No nonsofic group is known to be UQS or AQS. For sofic kernels the theorem
  recovers what soficity permanence already gives. The open input is `surjunctive-groups-are-uniformly-quantitatively-surjunctive`.
- **Payoff hosts.** Simple Kazhdan groups have no infinite amenable quotient, so the theorem does not reach them.

Proof: Section 3 of the linked artifact.
