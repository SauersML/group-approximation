---
rg: 2
id: coarse-reiter-radius-is-a-ball-compressed-walk-eigenvalue
kind: claim
title: In every finitely generated group the coarse Reiter radius needs only one test weight, the lazy-walk law, and equals up to a quadratic change of window the least ball on which the compressed lazy walk has top eigenvalue 1/2, so RGAP₁ is a Ramsey-versus-eigenvalue gap
distinct_from:
  coarse-ball-invariance-gives-fine-reiter-measures: that smooths one coarsely invariant measure into a finely invariant one; this starts from any vector on a ball with a single return inequality (no invariance at all), and from a single walk-weighted displacement bound, and closes the loop back to CR.
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that defines CR and proves RGAP₂ ⇒ ¬AMP ⇒ RGAP₁; this rewrites the CR side of RGAP₁ as a finite eigenvalue problem.
  small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2: that computes R and CR exactly at windows 1 and 2 by LPs; this gives an eigenvalue lower bound for CR at every window and computes it for F and F_2 to radius 9 and 8.
artifacts:
  - experiments/ball-compressed-walk-spectra-2026-09-17/ball_spectra.py
  - experiments/ball-compressed-walk-spectra-2026-09-17/f_R9.json
  - experiments/ball-compressed-walk-spectra-2026-09-17/f2_R8.json
---

**ESTABLISHED** by `coarse-reiter-radius-is-a-ball-compressed-walk-eigenvalue-proof`. It is a short direct proof
(Bhattacharyya bound, log-convexity of return moments, square back), in the style of
`coarse-ball-invariance-gives-fine-reiter-measures`. It holds in every group, has not been independently reviewed,
and no priority is claimed.

**Setting.** `G` is a group with finite generating set `S`, `S' = S ∪ S⁻¹ ∪ {e}`, `k = |S'|`, `B_r` is the word ball,
`(gν)(x) = ν(g⁻¹x)`, `‖·‖` is ℓ¹. `P = k⁻¹ Σ_{s∈S'} λ_s` and `Q = (I + P)/2`; `Q` is self-adjoint, `0 ≤ Q ≤ I`, and
`Q^t = Σ_g q_t(g) λ_g` for a probability `q_t` on `B_t` (the lazy-walk law). Three radius functions of `N ≥ 1`:

- `CR(N) = min{ r : some ν ∈ P(B_r) has ‖gν − ν‖ ≤ 1 for all g ∈ B_N }` (as in the gap node);
- `WR(N) = min{ r : some ν ∈ P(B_r) has Σ_g q_N(g) ‖gν − ν‖ ≤ 1 }` (one fixed test weight);
- `h(N) = min{ r : ρ(r, N) ≥ 1/2 }`, where `ρ(r, t) = max{ ⟨η, Q^t η⟩ : η ∈ ℓ²(B_r), ‖η‖₂ = 1 }` is the top
  eigenvalue of `Q^t` compressed to the finite space `ℓ²(B_r)`.

**Theorem.**
- **(1)** `WR(N) ≤ CR(N)` and `h(N) ≤ WR(N)`.
- **(2) Return gives coarse invariance.** If `η ∈ ℓ²(B_r)`, `‖η‖₂ = 1`, has `⟨η, Q^{2J} η⟩ ≥ a > 0`, then some
  `μ ∈ P(B_{r+J})` has `‖gμ − μ‖ ≤ 4|g|·√(k ln(1/a)/J)` for every `g ∈ G`. Hence `CR(M) ≤ r + J` whenever
  `J ≥ 16 k M² ln(1/a)`.
- **(3) Equivalence.** With `J_M = ⌈16 k M² ln 2⌉`:
  `h(M) ≤ WR(M) ≤ CR(M) ≤ h(2J_M) + J_M ≤ WR(2J_M) + J_M`.

So `CR`, `WR` and `h` agree up to the change of window `M ↦ 2J_M = O(kM²)` and an additive `O(kM²)`.

**Corollary (spectral RGAP₁).** In every infinite finitely generated group, each of the following is equivalent to
RGAP₁ ("for every `E` there is `N` with `CR(N) > exp_E(R(exp_E N))`", from
`thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`):
- (SGAP₁) for every `E` there is `N` such that every unit `η ∈ ℓ²(B_n)` with `n = exp_E(R(exp_E N))` has
  `⟨η, Q^N η⟩ < 1/2`;
- (WGAP₁) for every `E` there is `N` such that every `ν ∈ P(B_n)`, `n = exp_E(R(exp_E N))`, has
  `E_{g∼q_N} ‖gν − ν‖ > 1`.

For `F` this turns the Reiter side of the only necessary condition for ¬AMP into a finite symmetric-matrix
eigenvalue: RGAP₁ says the Ramsey radius stays non-elementarily below the radius at which the balls of `F` first carry
a vector returning with probability 1/2 after `N` lazy steps.

**Why it matters.**
- *The CR side has no quantifier left.* In the sibling lane's pairwise-Reiter node (id
  `ramsey-functions-are-pairwise-reiter-radii`, not yet on main when this was written), CR is "for every weight
  `w ∈ P(B_M)` some `ν`". Here one weight suffices, `w = q_N`, and then ℓ² turns the average of norms into one
  quadratic form: `Σ_g q_N(g)‖λ_gη − η‖₂² = 2 − 2⟨η, Q^N η⟩`. The whole quantifier exchange of RGAP₁ is now between
  `R` (for every pair `(α, β)` on `B_m` some `ν`, by the pair node) and one Rayleigh quotient.
- *What a route kill now needs.* The costly-amplification route dies iff CRE holds (gap node), iff, by (3), for some
  `E` and all `N`: some unit `η ≥ 0` on `B_n`, `n = exp_E(R(exp_E N))`, has `⟨η, Q^N η⟩ ≥ 1/2`. That is a single
  statement "Ramsey balance forces an ℓ² return" (RRET). The pair node's trivial classes (point-mass and commuting
  pairs) cannot supply it: in `F_2` every pair `(q_i, q_j)` of walk laws is ℓ¹-balanced (the lazy walk has
  `‖q_{L+1} − q_L‖ → 0` in every group), while `ρ(r, N) ≤ ‖Q‖^N` with `‖Q_{F_2}‖ = (6 + 2√3)/10 < 0.947`, so
  `h_{F_2}(N) = ∞` for `N ≥ 13`. Any RRET argument must use pairs that are not time shifts of one walk.
- *Computable lower bounds.* `CR(N) ≥ h(N)` is certified by one eigenvalue computation on `B_r`. For both `F` and
  `F_2` (`ball_spectra.py`), `h(1..5) = 0, 1, 1, 2, 2`; for `F`, `h(6) = 3` (`ρ_F(3,6) = 0.5351`). These are far below
  `CR_F(1) = 5`, so at small windows the ℓ² threshold 1/2 is loose and the eigenvalue certificate is weaker than the
  LP of `small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2`. Its value is asymptotic: it is monotone, finite
  linear algebra at every window, and it is sharp up to the polynomial change in (3).
