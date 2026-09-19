---
rg: 2
id: ramsey-functions-are-pairwise-reiter-radii
kind: claim
title: In every finitely generated group, Moore's function Ramsey radius R̃(m, ε, l) equals a weighted Reiter radius for l pairs of probability measures on B_m, so the set Ramsey radius R lies between the one-pair Reiter radii at thresholds 3/2 and 1 with no composition at all
distinct_from:
  small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2: that dualizes R into set certificates and CR into function certificates and computes them at small windows; this dualizes the function radius R̃ a second time, removing the test functions, and sandwiches R between two measure-pair radii.
  moore-ramsey-criterion-for-amenability: that quotes Towsner's Proposition 3.1, the one-way bound F(m, 2ε|S|) ≤ R̃(m, ε, |S|) through generator pairs; this is an exact equality for every l, with arbitrary pairs of measures instead of generators.
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that is the sandwich RGAP₂ ⇒ ¬AMP ⇒ RGAP₁ between R and CR; this rewrites the R side as a pair radius and splits RGAP₁ between two pair gaps.
  coarse-ball-invariance-gives-fine-reiter-measures: that smooths one coarsely invariant measure into a finely invariant one; this is a minimax identity for Moore's radii and uses no smoothing.
---

**ESTABLISHED** by `ramsey-functions-are-pairwise-reiter-radii-proof`. It is a direct proof from the definitions quoted
in `moore-ramsey-criterion-for-amenability` and the finite-dimensional von Neumann minimax theorem. It has not been
independently reviewed. The identity is elementary, and no priority is claimed beyond its use here.

**Setting.** `G` is a group, `S` a finite generating set, and `B_r` the ball of radius `r`. For finitely supported
measures, `(μν)(x) = Σ_{yz=x} μ(y)ν(z)`, so `gν(f) = Σ_x ν(x) f(gx)`. Put `N_{m,n} = {ν ∈ P(B_n) : P(B_m)ν ⊆ P(B_n)}`.
This is `P(I_{m,n})` with `I_{m,n} = {x : B_m x ⊆ B_n}`. Moore's radii are as quoted in
`moore-ramsey-criterion-for-amenability`:
- `R(m) = R(m, 1/2)` uses sets and `≤ 1/2`;
- `R̃(m, ε, l)` uses `l` functions `B_n → [0,1]` and `< ε`, with `R̃(m, ε) = R̃(m, ε, 1)`.

**Theorem.**
- **(A) Pair identity.** `R̃(m, ε, l) ≤ n` holds iff the following does. For every `w ∈ P({1,…,l})` and all
  `α_i, β_i ∈ P(B_m)`, some `ν ∈ N_{m,n}` has
  `Σ_i w_i ‖α_iν − β_iν‖_{ℓ¹} < 2ε`.
- **(B) One pair.** Write `PR_c(m)` for the least `n` such that every pair `α, β ∈ P(B_m)` admits `ν ∈ N_{m,n}` with
  `‖αν − βν‖₁ < c`. Then `R̃(m, ε) = PR_{2ε}(m)`, and for every `c > 3/2`
  `PR_c(m) ≤ R(m) ≤ PR_1(m)`.
- **(C) Coarse Reiter is the many-point-pair case.** Take `CR(M)` as in `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`:
  the least `r` such that some `ν ∈ P(B_r)` has `‖gν − ν‖₁ ≤ 1` for all `g ∈ B_M`. It is the least `r` such that, for
  every `w ∈ P(B_M)`, some `ν ∈ P(B_r)` has `Σ_g w_g ‖gν − ν‖₁ ≤ 1`. That is (A) with `l = |B_M|`, point pairs
  `(δ_g, δ_e)`, and no window constraint.
- **(D) Trivial pair classes.** In every group, a pair `(α, β)` in `P(B_m)` admits `ν ∈ N_{m,9m}` with
  `‖αν − βν‖₁ < 1` when either
  - `β = δ_b` is a point mass, or
  - `αβ = βα`.
- **(E) The thresholds really differ.** In `F_2 = ⟨a, b⟩`, the pair `α = (δ_a + δ_b)/2`, `β = (δ_{a⁻¹} + δ_{b⁻¹})/2`
  on `B_1` has `‖αν − βν‖₁ ≥ 1` for every finitely supported `ν`. So `PR_1(1) = R̃(1, 1/2) = ∞`, while `R(1) = 3`
  (`small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2`). The upper half of (B) can therefore fail by an infinite
  amount at a single window.

**Consequence for the Ramsey route (Corollary).** For each `c`, write PGAP_c for "for every `E` there is `N` with
`CR(N) > exp_E(PR_c(exp_E N))`". Then for every `c > 3/2`

PGAP_1 ⟹ RGAP₁ ⟹ PGAP_c,

where RGAP₁ is from `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`. Both implications are immediate from
(B), because `exp_E` is monotone.
