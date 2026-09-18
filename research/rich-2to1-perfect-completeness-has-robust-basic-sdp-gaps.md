---
rg: 2
id: rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps
kind: claim
title: For every delta > 0 there is n such that, for every eta > 0, some rich 2-to-1 instance with alphabets [2n], [n] has basic SDP value at least 1 - eta and integral value at most delta
distinct_from:
  walsh-frame-rich-2to1-games-have-value-near-one: that rules out one family of perfect SDP solutions as a gap; this asks whether any robust gap exists.
  sd-rich-and-unique-games-sos-gaps-interconvert: those gaps have completeness 1 - eta(n) with eta(n) tied to the alphabet, so at fixed n they do not beat a small threshold; this asks for every eta at fixed n.
---

**OPEN.** Proposed route: `robust-basic-sdp-gaps-from-rotated-frame-universe`.

This is the basic-SDP evidence question for BKM Conjecture 7 in the form that
matters at perfect completeness. If it is false, then for some `delta` and
every `n` there is `eta_0(n) > 0` such that basic SDP `>= 1 - eta_0(n)` implies
`val > delta`. That would be a polynomial-time algorithm for
`Gap-Rich-2-to-1_n[1, delta]` at every `n`, refuting Conjecture 7 unless
P = NP. If it is true, the basic SDP gives no such refutation, which is
consistent with the conjecture but proves nothing about hardness.

The GKOPTW Walsh-framed universe is not a witness
(`walsh-frame-rich-2to1-games-have-value-near-one`). The rotated-frame universe
is the surviving candidate. Its discretisation half is established; its
value half is open.

## Attempts

- 2026-09-17, e-ugc-pull-transplant (transplanter via finite-models):
  - Obvious witness: Khot--Vishnoi unique-games gaps, right-merged into rich
    games. It dies at the quantifier order. Their completeness is
    `1 - eta(n)` with `eta(n)` about `log(1/delta)/log n`, so at a fixed `n` a
    threshold `eta_0 < eta(n)` rejects them.
  - Second witness: GKOPTW Walsh-framed perfect solutions, enriched. It dies at
    forcing edge mass, which gives value `>= 1 - B(K)`.
  - Third witness: the rotated-frame universe `U_n`. It survives. The
    discretisation step is established. The value step is reduced to (A1) and
    (A2) in `rotated-frame-universe-rich-2to1-game-has-vanishing-value`, and
    every tested potential strategy decays like `n^(-0.2)` numerically.
- 2026-09-18, swarm-0917-w10-w10-ugc-pull (reframer via probability-random):
  **closed by the new route `robust-basic-sdp-gaps-from-gaussian-universe`.**
  - The witness is the Gaussian pair-sum universe `Gamma_(n,d)`. The left
    vertex is a `d x 2n` iid Gaussian matrix `G`, and the right vertex is
    `G M_P`. It is exactly rich.
  - Value side: `gaussian-universe-rich-2to1-game-has-vanishing-value`.
    - The reduction `val^4 <= 4 Stab_T(rho_A)` transfers verbatim. It uses only
      permutation invariance, richness, the fibre transport, and idempotence.
    - Here `T_P = Gamma(I tensor Pi_P)` is a second quantisation.
    - Splitting off `s = G 1` and bounding low chaos degrees by fibrewise
      Gaussian hypercontractivity (balance `E[rho | s] = 1/(2n)` is used
      fibre by fibre) gives
      `Stab <= 1/(2n) + e^2 D (ln 2n)^D/(2n) + lambda_D`, uniformly in `d`.
    - High degrees are bounded by
      `lambda_D = ||E_P Pi_P^(tensor D)|| <= 2^-ceil(D/2) + O_D(n^-1/2)`
      (`gaussian-pair-sum-chaos-eigenvalues-halve-every-two-degrees`,
      via an equality-pattern cell count). This is exact-checked for `n <= 5`.
  - SDP side: `gaussian-universe-discretises-to-robust-rich-2to1-sdp-gaps`.
    Polar-frame vectors have objective tending to 1 as `d -> infinity`. The
    finite discretisation follows `rotated-frame-universe-discretisation-proof`.
  - What stays open: the Haar-frame route
    `robust-basic-sdp-gaps-from-rotated-frame-universe` and its premise. The
    frame walk is not a second quantisation. The body's "OPEN" line above
    predates this route; status is carried by the route.
  - Consequence for BKM Conjecture 7: the basic SDP gives no thresholded-test
    refutation of `Gap-Rich-2-to-1_n[1, delta]`. This is consistent with the
    conjecture and proves no hardness.
