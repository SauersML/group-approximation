---
rg: 2
id: xor-cheeger-sdp-deficit-at-least-sqrt-gap-times-frustration
kind: claim
title: XOR Cheeger inequality -- every signed graph (every alphabet-2 unique game) with normalized spectral gap lambda and value 1 - gamma has XOR-SDP deficit at least sqrt(lambda) gamma / 27, and a polynomial-time rounding of any vector solution of deficit delta violates at most 27 delta / sqrt(lambda)
distinct_from:
  unique-games-on-expanding-constraint-graphs-are-easy: that is the AKKSTV rounding, val >= 1 - O((eta/lambda) log(lambda/eta)) for every alphabet, linear in 1/lambda; this is alphabet 2 only and improves 1/lambda to 1/sqrt(lambda), which is optimal up to the constant.
  akkstv-rounding-holds-on-all-loop-free-constraint-graphs: that extends the linear AKKSTV rounding to loop-free hosts; this is a different, sqrt-gap rounding for alphabet 2.
  spectral-gap-no-outputs-cannot-prove-ugc: that proves the linear gate val >= 1 - 768 eps/gamma - ... for every alphabet; this is the sqrt-gap gate at alphabet 2.
  expansion-certified-repetition-caps-deficit-ratio: that kills repetition rates linear in lambda gamma; this is the SDP inequality that makes sqrt(lambda) gamma rates certifiable at alphabet 2, and its consequence is recorded in lambda-gapped-xor-sources-cannot-feed-sqrt-rate-repetition.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that uses Raz's odd cycle (the domain wall) for a universal lower bound on repeated value; the odd cycle is the tightness example here.
  lambda-gapped-xor-sources-cannot-feed-sqrt-rate-repetition: that is the repetition and complexity consequence; this is the pure inequality.
artifacts:
  - experiments/ugc-xor-cheeger-2026-09-17/check_xor_cheeger.py
  - experiments/ugc-xor-cheeger-2026-09-17/output.txt
---

**ESTABLISHED.** Proof: `xor-cheeger-rank-one-rounding-proof` (self-contained,
elementary). This answers spark `4ee60ca4` (posted by `swarm-0917-w14-w14-ugc-last1`)
**positively**: the XOR Cheeger inequality holds with `c = 1/27`.

**Setting.** A signed graph is `(V, w, σ)`: nonnegative symmetric edge weights
`w_uv` and signs `σ_uv = σ_vu ∈ {±1}`. Equivalently, it is a unique game with
alphabet 2, or a Max-2LIN(F_2) instance, or a two-prover XOR game when the graph
is bipartite. Write `W = Σ_{u,v} w_uv`, and `P(u,v) = w_uv / deg(u)` for the
walk. The stationary law is `π(u) = deg(u)/W`. The edge law samples
`u ~ π`, `v ~ P(u, ·)`, so both endpoints have marginal `π`. The **gap** `λ` is
the second smallest eigenvalue of the normalized Laplacian `I − P`. For a
bipartite question graph this is the `λ` of AKKSTV and of
`akkstv-expansion-parallel-repetition-bound`.

* `val = max_{x ∈ {±1}^V} P_e[x_u = σ_uv x_v]`, and `γ = 1 − val`.
* `sdp = max E_e (1 + σ_uv ⟨x_u, x_v⟩)/2` over unit vectors `x_u`, and
  `δ_sdp = 1 − sdp`. For a vector solution `x`, its deficit is
  `δ(x) = E_e ‖x_u − σ_uv x_v‖² / 4`.

**Theorem.**

1. *(Rounding.)* For every vector solution `x` with deficit `δ = δ(x)`, a
   randomized polynomial-time rounding outputs `X ∈ {±1}^V` with
   `E[P_e(X violates e)] <= 27 δ / sqrt(λ)`. So `γ <= 27 δ_sdp / sqrt(λ)`.
2. *(XOR Cheeger inequality.)* `δ_sdp >= sqrt(λ) γ / 27`.
3. *(Basic SDP.)* The same lower bound holds for the basic unique-games SDP at
   alphabet 2, in both normalizations used in the graph: Figure 1 of AKKSTV
   (`E_i ‖u_i‖² = 1`, `⟨u_i,v_j⟩ >= 0`) and the basic SDP of
   `spectral-gap-no-outputs-cannot-prove-ugc` (`Σ_a ‖u_a‖² = 1`). Each of those
   has deficit `>= δ_sdp`.

**Tightness.** Raz's odd cycle, the domain wall, has `γ = 1/m`,
`δ_sdp = (1 − cos(π/m))/2` and `λ = 1 − cos(2π/m)`, so
`δ_sdp/(sqrt(λ) γ) -> π/(4 sqrt 2) ≈ 0.555`. The exponent `1/2` of `λ` is
therefore optimal, and the optimal constant lies in `[1/27, 0.556]`. The checker
confirms `0.557` on cycles of length 18.

**Why the linear bound improves.** AKKSTV-type arguments control only the
measure `τ` of the region where the SDP vectors leave the common direction. The
Poincaré inequality gives `τ <= 4δ/λ`. Here `τ` enters only under a square
root, `sqrt(τ · δ)`, by Cauchy–Schwarz. Frustration is charged either to the
energy of the twisted projection (sharp transitions) or to the measure of the
transition region (slow transitions). The first is `O(δ)`, the second
`O(δ/λ)`, and the violated mass is at most their geometric mean.

**Where the proof uses alphabet 2.** It uses Step 2, the projection to one
common line `w`. The label is then the sign of a single real twisted function.
For `k >= 3` the analogue fails uniformly in `k`: Khot–Vishnoi instances have
`δ_sdp ≈ λ` and `γ -> 1`, so `δ_sdp/(sqrt(λ) γ) ≈ sqrt(λ) -> 0`. What happens at
fixed `k >= 3` is the open question recorded in
`lambda-gapped-xor-sources-cannot-feed-sqrt-rate-repetition`.

**Numerical check.** `check_xor_cheeger.py` covers domain-wall cycles and tori,
ladders, flux hypercubes and random regular signed graphs. It checks Steps 1, 2
and 5 of the proof on Burer–Monteiro solutions, using the exact expectation
over the threshold and the hyperplane. It also checks exact `γ` by brute force
for `n <= 20`. All cases pass (`output.txt`).
