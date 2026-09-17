---
rg: 2
id: cluster-entropy-lower-bounds-need-nonpositive-total-weight-proof
kind: route
title: An invariant finite-set factor shifts a cluster functional by its total weight while a marker generator costs almost nothing
target: cluster-entropy-lower-bounds-need-nonpositive-total-weight
requires: []
artifacts:
  - research/artifacts/cluster-entropy-total-weight-obstruction-2026-09-17.md
  - experiments/cluster-weight-calibration-2026-09-17/check_cluster_weight.py
---

Complete direct proof: Theorem 1 and Corollary 2 of the artifact.

1. **The shift.** On `T = B × Y_m`, the fibre partition `R` is permuted by `G`, so `(P_e join R)^V = P_e^V join R`. `R` is uniform and independent of the coordinates, so `H(P_e^V join R) = H(P_e^V) + log m`. Summing with weights `c_W` gives `F((P_e join R)^(K_n)) = F(P_e^(K_n)) + kappa log m`, and `P_e join R` generates.
2. **The marker generator.** Let `E_0` be a cylinder of measure `eps = q^-k`, and put `R_E = {E^c} ∪ {E_0 × {c}}`. By ergodicity of `B`, a.e. orbit visits `E_0 × Y_m`, and the `R_E`-name there reveals `g c`, hence `c`. So `Q = P_e join R_E` generates, with `H(Q) <= log q + h(eps) + eps log m`.
3. **Compare.** (L) gives `beta + kappa log m <= log q + h(eps) + eps log m`. Letting `k -> infinity` gives `beta + kappa log m <= log q`, and then `kappa <= 0`, using infinitely many `m`, or one `m >= 2` when `beta >= log q`.
4. **Corollary.** The coefficients of a co-information `I_U` sum to 1, so `kappa(F_X) = chi(G\X)`. Co-information of coordinate partitions of an i.i.d. field is `|∩_(u in sigma) uK| log q`, so `F_X(P_e^K) = chi(X[K^-1]) log q`.
5. **Witness.** For `F_2 × F_2`, direct cell counts give `chi(G\X) = 1` and `chi(X[B_n × B_n]) = 1`, the latter as a product of finite trees.

The script checks items 1, 2, 4 and 5 by exact enumeration and cell counts.
