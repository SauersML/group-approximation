---
rg: 2
id: cluster-entropy-lower-bounds-need-nonpositive-total-weight
kind: claim
title: A cluster entropy functional that lower-bounds generating-partition entropy on Bernoulli shifts times finite sets has nonpositive total weight
distinct_from:
  window-entropy-deficits-are-not-isomorphism-invariant: that separates two generating partitions of one Bernoulli shift by window counts over a nonamenable group; this bounds the total weight of any cluster functional by testing it against an invariant finite-set factor and a marker generator.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that rules out invariants monotone under factors or weak containment; this rules out positive-weight cluster functionals with no monotonicity or invariance hypothesis.
  bowen-f-invariant-is-a-measure-conjugacy-invariant: that imports the invariance of Bowen's functional of total weight 1 - r on free groups; this shows every lower-bound functional must have total weight <= 0, so the Euler-weight generalizations with positive Euler characteristic fail.
artifacts:
  - research/artifacts/cluster-entropy-total-weight-obstruction-2026-09-17.md
  - experiments/cluster-weight-calibration-2026-09-17/check_cluster_weight.py
---

Let `G` be a countable group acting by measure-preserving maps. For a finite partition `P` and a finite `W ⊆ G`, put `P^W = join_(w in W) wP`. A finite cluster functional is

    F(P) = sum_(W in 𝒲) c_W H(P^W),

and its **total weight** is `kappa(F) = sum_W c_W`. Fix finite sets `K_n ⊆ G` and `q >= 2`, and let `B` be the uniform Bernoulli shift `q^G` with time-zero partition `P_e`. Suppose:

- **(L)** `liminf_n F(P^(K_n)) <= H(Q)` for all finite generating partitions `P`, `Q` of every action in a class `𝒞`;
- **(N)** `B` is in `𝒞`, and `beta = liminf_n F(P_e^(K_n)) > -infinity`;
- **(Y)** `𝒞` contains `B × Y_m` for infinitely many `m`, where `Y_m` is `m` points with uniform measure and any action by permutations, for example the trivial one. If `beta >= log q`, one `m >= 2` suffices.

Then `kappa(F) <= 0`.

**Proof in one line.** `R` is the invariant `m`-fibre partition, and `Q_k = P_e join R_E` records the fibre only on a cylinder of measure `q^-k`. Then (L) gives `beta + kappa log m = liminf F((P_e join R)^(K_n)) <= H(Q_k) <= log q + h(q^-k) + q^-k log m -> log q`.

**Cellular corollary.** Let `X` be a complex with vertex set `G`, free left action on cells and finitely many cell orbits, and let `F_X = sum_(orbit reps sigma) (-1)^(dim sigma) I_sigma`, with `I_sigma` the co-information of `{uP : u in sigma}`. Then `kappa(F_X) = chi(G\X)`. On `B`, `F_X(P_e^K) = chi(X[K^-1]) log q`.
- If `chi(G\X) > 0`, `F_X` is not a lower bound on any class satisfying (N) and (Y), whatever the exhaustion.
- **Witness:** `F_2 × F_2` with the product-of-trees square complex. It has `kappa = 1 - 4 + 4 = 1`, and `chi(X[B_n × B_n]) = 1`, so `beta = log q`. On `B × Y_2` its value is `log q + log 2`, while generators of entropy arbitrarily close to `log q` exist.
- Bowen's functional on `F_r` has `kappa = 1 - r <= 0` and passes.

**Scope.** On a finitely generated simple Kazhdan host there are no nontrivial finite actions. There the kill applies to mechanisms asserted for all pmp actions with finite generating partitions, nonergodic ones included, as Bowen-style splitting arguments are. Ergodic-only mechanisms and functionals with `kappa <= 0` are not touched.

**ESTABLISHED 2026-09-17** by
[[cluster-entropy-lower-bounds-need-nonpositive-total-weight-proof]].
