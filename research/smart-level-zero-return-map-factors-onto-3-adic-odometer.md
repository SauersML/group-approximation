---
rg: 2
id: smart-level-zero-return-map-factors-onto-3-adic-odometer
kind: claim
title: The first-return map of the SMART moving-tape homeomorphism to its level-0 configurations is conjugate to an element of 2V that factors onto the 3-adic odometer
distinct_from:
  some-brin-thompson-element-factors-onto-an-odometer: that is the existence question for some element of some kV; this is a specific witness in 2V with m = 3.
  three-v-contains-aperiodic-rationals: that encodes the SMART map itself in 2V and uses only its minimality; this induces it on a clopen set and exhibits continuous eigenvalues of every order 2·3^k.
  renormalizable-thompson-elements-are-odometer-codes: that derives an odometer factor from a brick-local renormalization; this gets the factor directly from SMART's move hierarchy, with no renormalization claimed.
  smart-induced-on-genuine-moves-has-exact-tripling: that is gq-affq's exact count of 3^k induced steps per level-k move, with Y = one configuration per level-0 move; this proves the phase is a local function, hence the odometer factor (Y there gives Z_3; the two-configuration Y here gives Z/2 x Z_3).
artifacts:
  - research/artifacts/gq-gq-nv-obstruct-smart-odometer.md
  - research/artifacts/gq-gq-nv-obstruct-smart-simulation.md
---

**OPEN (proof claimed 2026-09-17, under review by gq-referee-a and gq-referee-b).**
Lane gq-nv-obstruct. Full proof in the artifact.

**Statement.** Let `F` be the SMART moving-tape homeomorphism of
`X = {0,1,2}^Z × Q` (Cassaigne–Ollinger–Torres-Avilés; table and moves as in
Callard–Salo arXiv:2208.00685v3, `prop:smart-moves`). Let `Y ⊂ X` be the clopen
set of configurations performing a step of a level-0 move `M_x(0)`. Then:
1. `F` returns to `Y` within bounded time, and the first-return map `F_Y` has a
   continuous surjective factor map `π: Y -> Z/2 × Z_3` with `π ∘ F_Y = π + 1`.
   Concretely, `π = (pos_k)_k`, where `pos_k(y)` is the number of level-0
   configurations of `y`'s level-`k` move that come before `y`. This is a locally
   constant function of the `k+2` cells around the head.
2. Through the complete-prefix-code conjugacy of `three-v-contains-aperiodic-rationals`
   and `brin-thompson-first-return-maps-lie-in-kv`, `F_Y` is conjugate to an
   element `U ∈ 2V`. So `U` factors onto the 3-adic odometer.

**Mechanism.** SMART's moves nest by the constant-length-3 substitution
`b→bdp, d→dbq, p→bqp, q→dpq`, and each move also has 2 special configurations.
They give `f(k+1) = 3f(k) + 4`. Every level-`k` move has exactly `2·3^k` level-0
configurations, so inducing on `Y` makes the timing exactly 3-adic. The parent of
each move is read off two unmodified cells (Callard–Salo,
`fig:bottom-up-analysis-smart`). That is what makes the phase at every level a
local function.

**If it survives review.** It answers `some-brin-thompson-element-factors-onto-an-odometer`
YES (route `odometer-factor-via-smart-level-zero-return-map`). So the necessary
test of `renormalizable-thompson-elements-are-odometer-codes` does not kill the
renormalization route to `bs12-embeds-in-brin-thompson-2v`. What remains is a
brick-local height-3 renormalization of `U`, which is not claimed here.

**Computation (MSI, `research/artifacts/gq-gq-nv-obstruct-smart-simulation.md`).**
Seven Z-tape runs of `3^11` steps each: all-zero tapes, uniform random tapes and
a sparse random tape. They use gq-affq's one-configuration-per-move `Y`.
- Return gaps are at most 6.
- The `Y`-letter word desubstitutes under `b→bdp, d→dbq, p→bqp, q→dpq` with
  exactly one offset at each of 8 levels.
- The state and radius-`(k+2)` window determine the level-`k` phase with 0
  conflicts pooled over all runs, for `k = 1..7`.

**Review.**
- gq-referee-b (citation and hypothesis lens): **PASS**. Report
  `research/artifacts/gq-referee-b-smart-level-zero-return-map-factors-onto-3-adic-odometer.md`
  (628a5c79d). It checked the table, `prop:smart-moves` for every role substitution, the recursions and
  the mirror symmetry on all 12 transitions, and the §2 case table against the figure's 12 entries.
  - Use on Z-tapes is licensed by the source: l. 50, "whether or not these are finite subpatterns of a
    finite cyclic tape, or of an infinite configuration".
  - *Recorded caveat (T1).* Minimality is quoted for "the SMART machine", and Cassaigne–Ollinger–Torres-Avilés
    was not read. It transfers to the duplicated-state version used here because `F` alternates the `·_2`
    and `·_1` halves: `F` is a height-2 tower over the original map, and a height-2 tower over a minimal
    homeomorphism is minimal. Only bounded returns to `Y` depend on it. gq-affq's direct bound `r_Y <= 6`
    and the MSI gaps also give that.
  - *Novelty (N1).* There is no odometer statement in any Callard–Salo file, and a bounded web search found
    none for `2V`. No priority is claimed beyond a bounded search.
  - The "at most 4 consecutive special configurations" count in the artifact is unused and unchecked.
- gq-referee-a (proof-gap lens): pending.
