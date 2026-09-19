---
rg: 2
id: fpbs-t4xz-certified-critical-l2-gap
kind: claim
title: T_4 x Z = Cay(F_2 x Z, standard) has p_c <= 0.236 < 0.241 <= p_{2->2}, and every T_2k x Z with k >= 2 has a critical l2 gap
distinct_from:
  fpbs-rigid-f2xz-certified-strict-thresholds: that certifies the 14-regular rigid decoration S_rig of F_2 x Z with a star-stage GW; this certifies the standard 6-regular generating set, where the star stage adds nothing (back ladder edges coincide with entry edges) and a closed-form one-type fibre-interval GW suffices.
  fpbs-weighted-surface-continuity-reduces-to-uniform-floor: that leaves F_2 x Z (k=2) open unless p_c(T_4 x Z) < 0.21085, and Monte Carlo puts p_c(T_4 x Z) near 0.212, so the tree anchor cannot work; this replaces the tree anchor by a cycle-avoiding Busemann Schur bound reaching 0.2412 and certifies k = 2 and k = 3.
  fpbs-expanding-factor-product-strict-thresholds: that covers T_2k x Z only when 2k-1 > 2 sqrt(2k-1) + 2, i.e. k >= 5; this adds k = 2, 3, 4.
  fpbs-two-point-lq-threshold-gap-universal: that is the open universal hole [Q]; this verifies [Q], and p_c < p_2, on the canonical unimodular product T_4 x Z where no qualitative theorem recorded in the graph applied.
artifacts:
  - experiments/fpbs-t4xz-certificate-2026-09-17/rho2v.py
  - experiments/fpbs-t4xz-certificate-2026-09-17/certschur.py
  - experiments/fpbs-t4xz-certificate-2026-09-17/certify_all.py
  - experiments/fpbs-t4xz-certificate-2026-09-17/mc.c
  - experiments/fpbs-t4xz-certificate-2026-09-17/outputs.txt
---

**ESTABLISHED** (written proof in `fpbs-t4xz-certified-critical-l2-gap-proof`,
plus exact rational and integer certificates).

Let `X_k = T_{2k} x Z = Cay(F_k x Z, {a_1, ..., a_k, t})`, which is
`(2k+2)`-regular. For Bernoulli bond percolation on `X_k`:

| `k` | certified `p_c <=` | certified `<= p_{2->2}` | method for `p_{2->2}` |
|---|---|---|---|
| 2 | `236/1000` | `241/1000` | cycle-avoiding (`ell = 4`) Busemann Schur test, `lambda <= 829/200` |
| 3 | `1544/10000` | `1545/10000` | `1/||A||`, `||A|| = 2 + 2 sqrt 5` |
| 4 | `12/100` | `13/100` | `1/||A||`, `||A|| = 2 + 2 sqrt 7` |
| `>= 5` | just above `1/(2k-1)` | `1/(2+2 sqrt(2k-1))` | `1/||A||` (already known) |

So `p_c(X_k) < p_{2->2}(X_k) <= p_u(X_k)` for every `k >= 2`.

**The two ingredients.**
1. **Fibre-interval Galton-Watson bound on `p_c`.** One individual is a fibre
   `{w} x Z` entered at one height. Its stage reveals the open vertical
   interval through the entry height, then, for each of the `2k-1` child
   letters, the ladder edges out of that interval until the first open one. The
   process is one-type with mean
   `m_k(p) = (2k-1)(1 - (1-p) phi^2)`, where `phi = (1-p)/(1-p+p^2)`. So
   `m_k(p) > 1` implies `theta(p) > 0`. The root of `m_k = 1` is `0.234307`
   for `k = 2` and `0.154313` for `k = 3`.
2. **Busemann Schur test for `k = 2`.** `tau_p` is dominated by the sum of
   `p^n` over walks with no cycle of length `<= 4`. The walks are weighted by
   `u^(-beta)`, where `beta` is a Busemann function of `T_4` and
   `u = 1732/1000`. An exact integer check over 150 step-states times 4 letters
   gives the transfer inequality with `lambda = 829/200`. The non-backtracking
   bound (`ell = 2`) gives only `0.23246`, which is below the GW root, so
   forbidding the commutator 4-cycles `[a,t]`, `[b,t]` is what closes the gap.

**Consequences for `X_k`, `k >= 2`.**
* Benjamini–Schramm, `p_c < p_u`, holds for the standard generating set of
  `F_k x Z`. The graph records Grimmett–Newman nonuniqueness on `T_d x Z` only
  for large `d`, and `fpbs-expanding-factor-product-strict-thresholds` only
  for `k >= 5`.
* [Q] holds: `tau <= 1` gives `Z_q <= Z_2`, so `p_c < p_{2->2} <= p_2 <= p_q`
  for every `q >= 2`. In particular `q_0(X_k) < 2`.
* By the chain in `fpbs-two-point-fourier-algebra-criterion` and
  `fpbs-flat-walk-rate-past-pc-universal`, [A] and [F] hold on `X_k`, and so
  does (IS).

**Calibration.** Monte Carlo (`mc.c`) puts `p_c(T_4 x Z)` near `0.212`. That is
just above the tree anchor `0.21085`, which therefore fails, as the anchor claim
feared. It is far below the Schur bound `0.2412`. `p_{2->2}(T_4 x Z)` itself is
not estimated. The Schur values continue to `0.24317` at `ell = 6` and
`0.24380` at `ell = 8`.

**Scope and what it does not do.** This is one graph family. It gives no uniform
mechanism: the GW bound uses that the vertical fibre is a line entered once, and
the Schur bound uses the tree Busemann function. It is the first case of the
target table where every qualitative and one-step anchor theorem in the graph
failed, and it shows that the critical `l^2` gap there is not marginal: the
certified window `[0.236, 0.241]` sits about 11% above the Monte Carlo `p_c`.
