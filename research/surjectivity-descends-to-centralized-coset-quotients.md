---
rg: 2
id: surjectivity-descends-to-centralized-coset-quotients
kind: claim
title: Surjectivity of an injective automaton descends to its quotient automaton over a subgroup centralizing the memory
distinct_from:
  surjunctivity-passes-to-subgroups: that transfers surjunctivity of a group to its subgroups; this transfers surjectivity of one injective automaton to its induced automaton over N_G(B)/B for a subgroup B centralizing the memory, so strictness ascends from central quotients of the memory group.
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Let `tau` be an automaton over `G` with memory `M` and rule `mu`, and let `B <= G` commute
elementwise with `M`.

- **Invariance:** `tau` commutes with the right translations `R_b` (`b in B`), and it preserves
  `Y_B = {x : x(gb) = x(g)} = A^(G/B)`.
- **Quotient automaton:** the group `Q = N_G(B)/B` acts freely on `G/B` from the right. On each
  orbit, `tau` restricted to `Y_B` is the automaton `taubar` over `Q` with memory `MB/B` and rule
  `mubar(z) = mu((z(mB))_(m in M))`.
- **Transfer:** if `tau` is injective, `taubar` is injective. If `tau` is bijective, `taubar` is
  bijective.

So:
- if `tau` is injective and `taubar` is not surjective, `tau` is strict;
- over a surjunctive group, every injective automaton whose memory centralizes `B` has a surjective
  quotient.

Only `Gamma/(Gamma meet B)` matters, for the effective memory group `Gamma`, and `Gamma meet B` is
central in `Gamma`. So strictness ascends from central quotients of the memory group to injective
lifts, and surjectivity descends.

Theorem 2 of the artifact.
