---
rg: 2
id: maximal-bernoulli-rokhlin-entropy-makes-groups-uqs-proof
kind: route
title: Let the number of amplified copies grow so that the fixed marker cost vanishes against the deficit
target: maximal-bernoulli-rokhlin-entropy-makes-groups-uqs
requires: [subshift-track-injections-lower-rokhlin-entropy, seward-per-group-rokhlin-entropy-of-bernoulli-shifts]
artifacts:
  - research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md
---

Section 2 of the artifact.

- **Threshold.** Maximality makes the left side of the first prerequisite equal to `k (n log b + j log|D|)`. So
  `k (mu - Sigma) >= -m log 3` for every `k`, and `mu >= Sigma`. Item 1 of the second prerequisite shows that
  maximality at every alphabet is `h^Rok_sup(G) = infinity`.
- **Constants.** `|W_i| <= w` gives `eta_i >= -log(1 - |B|^-w)` and `D_i <= w^2`, so `Sigma >= n delta(B, w)`. With
  one subshift on every track, `Sigma = n eta_W / |W W^-1|`.
- **Finite groups.** A maximal `C` with `C C^-1` disjoint from `W W^-1 \ {1}` has `|C| >= |G| / |W W^-1|`, and the
  windows `c^-1 W`, `c in C`, are disjoint. Counting configurations of each track gives `mu >= Sigma`.
- **Supremum bound.** `k_0 (Sigma - mu) > m log 3`, so at `k = k_0` the first prerequisite gives an entropy below the
  base entropy. By item 1 of the second prerequisite that entropy is `h^Rok_sup(G)`.

Independent re-derivation requested from w4-vf-positive-b.
