---
rg: 2
id: subshift-track-injections-lower-rokhlin-entropy
kind: claim
title: An injective automaton into proper subshift tracks and a free track lowers the Rokhlin entropy of amplified Bernoulli shifts
distinct_from:
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that is one copy of the full shift whose image misses one cylinder; this allows many tracks missing different patterns plus free full-shift tracks of different sizes on the two sides, the shape quantitative surjunctivity needs.
  quantitative-surjunctivity-constants-lift-from-quotients: that gets constants by restricting to configurations invariant under a normal subgroup; this never evaluates an invariant configuration, which is a null set, and bounds an isomorphism invariant instead.
artifacts:
  - research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by [[subshift-track-injections-lower-rokhlin-entropy-proof]].

Let `G` be a countably infinite group, `B` and `D` finite alphabets with `b = |B| >= 2`, and `n >= 1`, `j, j' >= 0`.
Let `Y_1, ..., Y_n <= B^G` be subshifts, `Y_i` missing a pattern on the finite window `W_i`. Let `Phi` be an injective
cellular automaton from `(B^n x D^j)^G` into `Y_1 x ... x Y_n x (D^(j'))^G`. Put

    eta_i = -log(1 - b^-|W_i|),    D_i = |W_i W_i^-1|,    Sigma = sum_i eta_i / D_i,

and let `m` be the number of distinct sets among `W_1, ..., W_n`. Then for every `k >= 1`

    h^Rok_G((B^(nk) x D^(jk))^G, uniform) <= k (n log b + j' log|D| - Sigma) + m log 3.

- **Special case.** `n = 1`, `j = j' = 0`, with `Y_1` the image of a strict automaton, is
  `strict-automaton-lowers-bernoulli-rokhlin-entropy`.
- **Invariant configurations.** The pushed-forward measure gives measure zero to every configuration invariant under
  a nontrivial normal subgroup, constants included. So the bound does not care whether the tracks contain such
  configurations, and it applies to the residue of `quantitative-surjunctivity-constants-lift-from-quotients`, where
  restriction and fixed-point counting give nothing.
- **Where it stops.** It turns quantitative surjunctivity into a lower bound on Rokhlin entropy. Such bounds are known
  only on groups with maximal Bernoulli Rokhlin entropy (`maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`).

Section 1 of the artifact.
