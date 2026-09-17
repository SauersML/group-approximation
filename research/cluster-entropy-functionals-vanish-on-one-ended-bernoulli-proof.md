---
rg: 2
id: cluster-entropy-functionals-vanish-on-one-ended-bernoulli-proof
kind: route
title: Exact inclusion-exclusion for the window valuation on a fat digon built from a geodesic and a detour
target: cluster-entropy-functionals-vanish-on-one-ended-bernoulli
requires: []
artifacts:
  - research/artifacts/cluster-entropy-functionals-one-ended-obstruction-2026-09-17.md
  - experiments/cluster-entropy-functionals-2026-09-17/check_cluster_valuation.py
---

Complete direct proof, Sections 1–3 of the artifact.

1. **Valuation.** On a Bernoulli shift with base law `p`, `join_{w in W} w^-1 Q_B = Q_{BW}` and
   the coordinates are independent. So `F(Q_B) = H(p) psi(B)` with `psi(B) = sum_W c_W |BW|`,
   and `psi` is left-invariant.
2. **Lemma 2.2 (exact).** Let `C = B_1 ∩ B_2` and `R = max |w' w^-1|`. If
   `d(B_1 \ C, B_2 \ C) > R`, then `B_1W ∩ B_2W = CW`: if `b_1 w = b_2 w'` with `b_i` outside
   `C`, then `d(b_2, b_1) = |w' w^-1| <= R`. Hence
   `psi(B_1 u B_2) = psi(B_1) + psi(B_2) - psi(C)`.
3. **Lemma 2.3.** Splitting monotonicity with `gamma` a single coordinate adds one neighbour
   `dt` at a time. So `psi(D') <= psi(D)` for `D ⊆ D'` with `D'` connected, by breadth-first
   growth.
4. **Proposition 3.1.** On an `R`-fat digon `(B_1, B_2, C', C'')`:
   `psi(B_1 u B_2) = psi(B_1) + psi(B_2) - psi(C') - psi(C'') <= 0`. Then every connected `D`
   containing `B_1 u B_2` has `psi(D) <= 0`.
5. **Proposition 3.2.** In a one-ended group, take a bi-infinite geodesic `l` with `l(0) = e`
   (König) and put `Delta = 2R + 4`, `L = Delta + 1`, `a = R + 2`. There is a path `pi` from
   `l(-L)` to `l(L)` avoiding `B_Delta`, because both rays lie in the unique infinite component.
   The digon is:
   - `B_1 = l[-a-R-1, a+R+1]`;
   - `B_2 = pi u l[-L, -a-1] u l[a+1, L]`;
   - `C' = l[-a-R-1, -a-1]` and `C'' = l[a+1, a+R+1]`.

   Its distances are checked from geodesicity and from `pi ∩ B_Delta = ∅`.

The script checks the valuation identity and the digon hypotheses numerically over `Z^2`, where
Bowen's `r = 2` functional gives `psi = 0` on the digon union and `-59` on the L1-ball of
radius 6. It also checks `psi = 1` on random subtrees of `F_2`, the calibration case with no
fat digon.
