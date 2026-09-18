---
rg: 2
id: hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-proof
kind: route
title: Record the forward-bad layers as a full track and apply one UQS constant over a free product of deck groups
target: hull-irs-strict-designs-force-nonsurjunctive-or-non-uqs-groups
requires:
  - atomic-irs-strict-designs-are-nonsurjunctive-quotients
  - amenable-extensions-of-uqs-groups-are-surjunctive
artifacts:
  - research/artifacts/atomic-hull-uqs-transfer-2026-09-17.md
---

Complete proof: artifact Section 3. The layer identification comes from the proof of
`atomic-irs-strict-designs-are-nonsurjunctive-quotients`. The UQS definition and subgroup heredity with the
same constants come from `amenable-extensions-of-uqs-groups-are-surjunctive` (Proposition 3.1 of its
artifact). Curtis-Hedlund-Lyndon over arbitrary groups is imported.

1. **Layers.** An ergodic atomic `nu` has Schreier graph `Q x {1..k}`, with `Q` acting freely by
   label-preserving automorphisms. Goodness and badness depend only on the layer, so `eps_D(nu) = |E|/k`
   and `delta_D(nu) = |R|/k`.
2. **Injective automaton.** `T(x) = (tau x, x|_(Q x E))` is an injective cellular automaton over `Q`,
   since forward-good layers are recovered by `sigma`.
3. **Excluded patterns.** A reverse-bad layer whose `R_tau`-ball in `X_0 = N(H)\F_m` avoids `E` is clean.
   The image `tau x` misses the witness pattern at every `Q`-translate. There are at least
   `|R| - d_(R_tau) |E|` clean layers.
4. **Tracks.** Greedy `2 rho`-separation in `X_0` gives `n >= |clean| / d_(2 rho)` disjoint layer balls,
   each with at most `d_rho` layers. Pad the tracks with fresh copied coordinates to the alphabet
   `A^(d_rho)`. Each track lies in a subshift missing a pattern on at most `d_rho` sites, and the full track
   grows by exactly `|E|` coordinates.
5. **Deficit.** UQS forces `|E| ln|A| >= delta_Q(A^(d_rho), d_rho) n`, which gives
   `delta_D <= C eps_D` with `C` independent of `nu`.
6. **Limit.** Approximate `mu` by finite mixtures of countably many atomic `nu`. Let `G` be the free
   product of their finitely generated deck groups.
   - If `G` is non-surjunctive, or surjunctive and not UQS, we are done.
   - Otherwise heredity gives one constant function for all components. Affinity and continuity of
     `eps_D` and `delta_D` then give `delta_D(mu) <= C eps_D(mu) = 0`, a contradiction.
