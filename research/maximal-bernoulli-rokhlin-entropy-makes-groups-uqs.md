---
rg: 2
id: maximal-bernoulli-rokhlin-entropy-makes-groups-uqs
kind: claim
title: A group whose uniform Bernoulli shifts have maximal Rokhlin entropy is uniformly quantitatively surjunctive with explicit constants
distinct_from:
  infinite-rokhlin-supremum-forces-surjunctivity: that imports Seward's implication from an infinite supremum to surjunctivity; this derives the stronger deficit for injections into proper subshift tracks, with explicit constants, and bounds the supremum from one sub-threshold injection.
  surjunctive-groups-are-uniformly-quantitatively-surjunctive: that asks for the deficit on every surjunctive group; this proves it on groups with maximal Bernoulli Rokhlin entropy, a class not known to contain any nonsofic group.
  strict-automaton-bounds-rokhlin-supremum: that bounds the supremum from one strict automaton; this bounds it from any injection into proper subshift tracks with margin below the threshold, which a strict automaton provides.
artifacts:
  - research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by [[maximal-bernoulli-rokhlin-entropy-makes-groups-uqs-proof]].

Notation as in `subshift-track-injections-lower-rokhlin-entropy`, with margin `mu = (j' - j) log|D|`.

1. **Threshold.** Let `G` be countably infinite with `h^Rok_G(A^G, uniform) = log|A|` for every finite alphabet `A`,
   equivalently `h^Rok_sup(G) = infinity`. Then every injective automaton from `(B^n x D^j)^G` into
   `Y_1 x ... x Y_n x (D^(j'))^G` has `mu >= Sigma`. Finite groups satisfy the same bound with no hypothesis.
2. **Constants.** So such a group is uniformly quantitatively surjunctive in the sense of
   `amenable-extensions-of-uqs-groups-are-surjunctive`, with `delta(B, w) = -log(1 - |B|^-w) / w^2`. It is
   quantitatively surjunctive in the sense of `surjunctive-groups-are-quantitatively-surjunctive`, with
   `delta_Y = -log(1 - |B|^-|W|) / |W W^-1|` for a pattern on `W` missing from `Y`.
3. **Supremum bound.** Let `G` be any countably infinite group carrying such an injection with `mu < Sigma`. Put
   `k_0 = floor(m log 3 / (Sigma - mu)) + 1`. Then

       h^Rok_sup(G) <= k_0 (n log b + j' log|D| - Sigma) + m log 3 < k_0 (n log b + j log|D|).

   So a group that is not quantitatively surjunctive has finite Rokhlin supremum. If it also contains its own square
   and finite subgroups of unbounded order, the supremum is `0`
   (`rokhlin-supremum-dichotomy-with-centralized-self-copies`).

**Scope.**
- Every group currently known to have maximal Bernoulli Rokhlin entropy is sofic
  (`rokhlin-maximality-ascends-co-amenable-subgroups`). So no new group becomes quantitatively surjunctive.
- The constant `eta / |W W^-1|` is at least the sofic constant `eta / (|W|^2 + 1)`.
- Part 3 with `n = m = 1`, `j = j' = 0` recovers `strict-automaton-bounds-rokhlin-supremum` with the same `k_0`.

Section 2 of the artifact.
