---
rg: 2
id: f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent
kind: claim
title: The rare-confinement exponent of the dyadic inverted orbit is minus the log of a cylinder-compressed Koopman norm, at most the cogrowth exponent of F, and invisible to every Walsh-level spectral gap
distinct_from:
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open statement that the exponent is 0; this proves the exponent exists, is a single operator norm, is at most minus the log of the Kesten radius of F, and is not detected by any Walsh-level spectral gap, without deciding whether it is 0.
  f-dyadic-ea-iff-inverted-orbit-confinement: that is the cited qualitative equivalence of extensive amenability with vanishing exponent; this turns the exponent into an operator norm and bounds it by the cogrowth of F and by bounded-depth band exponents.
  thompson-f-dyadic-ea-witnesses-need-tower-size: that bounds the size of finite extensive-amenability witnesses from Moore's theorem; this is a spectral identity and a squeeze for the confinement exponent, with no size bounds.
  f-dyadic-action-is-not-recurrent: that gives the linear mean of the inverted orbit; this concerns the exponential cost of confinement, which the mean does not see.
  kesten-amenable-stabilizer-uniform-gap: that is a spectral gap on coset spaces of amenable subgroups; this uses it for the lower half of the squeeze and shows it gives nothing for F, where every Walsh level has top spectrum 1.
artifacts:
  - experiments/f-dyadic-rare-confinement-2026-09-17/cloning.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/cloning_main.json
  - experiments/f-dyadic-rare-confinement-2026-09-17/cloning_main.log
  - experiments/f-dyadic-rare-confinement-2026-09-17/band_long.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/band_F.json
  - experiments/f-dyadic-rare-confinement-2026-09-17/band_F.log
  - experiments/f-dyadic-rare-confinement-2026-09-17/band_PSL.json
  - experiments/f-dyadic-rare-confinement-2026-09-17/band_PSL.log
  - experiments/f-dyadic-rare-confinement-2026-09-17/lambda_long.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/lambda_F.json
  - experiments/f-dyadic-rare-confinement-2026-09-17/lambda_F.log
  - experiments/f-dyadic-rare-confinement-2026-09-17/lambda_PSL.json
  - experiments/f-dyadic-rare-confinement-2026-09-17/lambda_PSL.log
  - experiments/f-dyadic-rare-confinement-2026-09-17/psl_return.py
  - experiments/f-dyadic-rare-confinement-2026-09-17/psl_return.log
---

**ESTABLISHED** through `f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent-proof` (direct proof from
Kesten's criterion, Perron–Frobenius and the established nodes it requires; not independently reviewed; no
priority claimed). The numerical part is supporting evidence only and is not used in any proof.

**Setting.** Let `G` be a countable group acting transitively on a set `X`, let `x_0 ∈ X`, and let `μ` be a
symmetric, finitely supported probability measure on `G` whose support generates `G`. Let `g_n = h_n⋯h_1` be
the left random walk and `O_n = {x_0, g_1⁻¹x_0, …, g_n⁻¹x_0}` the inverted orbit. Let `m` be the Bernoulli(1/2)
product measure on `Ω = {0,1}^X`, with `G` acting by `(gω)(x) = ω(g⁻¹x)`. Let `π(g)f = f∘g⁻¹` be the Koopman
representation on `L²(Ω,m)`, `P = Σ_h μ(h)π(h)`, and `E = {ω : ω(x_0) = 0}`. Put `Q = 1_E P 1_E` on `L²(E)`.

Let `ρ = ρ(G,μ)` be the norm of `P` on `ℓ²(G)` (the Kesten radius). Let `ρ_k` be the top of the spectrum of
`P` on `ℓ²(P_k(X))`, where `P_k(X)` is the set of `k`-element subsets of `X` with the permutation action, and
let `ρ_0^+ = sup_{k≥1} ρ_k`.

**Theorem.**

1. **(Koopman identity.)** `E 2^{−|O_n|} = ⟨Q^n 1_E, 1_E⟩` for every `n`. The limit
   `Λ(G↷X,μ) = lim −(1/n) log E 2^{−|O_n|}` exists and equals `−log ‖Q‖`.
2. **(Cylinder almost-invariant sets.)** `Λ = 0` if and only if for every `ε > 0` there is a measurable
   `A ⊆ E` with `m(A) > 0` and `Σ_h μ(h) m(hA Δ A) ≤ ε m(A)`.
3. **(Cogrowth upper bound.)** `Λ ≤ −log ρ(G,μ)`. For `F = ⟨x_0,x_1⟩` acting on the dyadics `D ⊂ (0,1)` with
   `μ` uniform on `{x_0^{±1}, x_1^{±1}}`, `Λ_F ≤ −log 0.901532 < 0.10366`
   (`thompson-f-norm-bound-from-hhr-exact-moments`).
4. **(Toggle lower bound and squeeze.)** `Λ ≥ −log((1+ρ_0^+)/2)`. Suppose `μ` is uniform on a finite symmetric
   generating set, and the setwise stabilizer of every nonempty finite subset of `X` is amenable. Then
   `ρ_0^+ ≤ ρ`, so `−log((1+ρ)/2) ≤ Λ ≤ −log ρ`. In particular `Λ = 0` for such an action iff `G` is
   amenable (Kesten), and as `ρ → 1` the two bounds differ by a factor tending to 2.
5. **(Class kill for F.)** For `F ↷ D` and every symmetric `μ` supported on `{x_0^{±1}, x_1^{±1}}`, `ρ_k = 1`
   for every `k ≥ 1`, so `ρ_0^+ = 1` and the bound in (4) is the trivial `Λ ≥ 0`.
6. **(Band completeness for F.)** Let `D_C = {j/2^C : 0 < j < 2^C}`, `x_0 = 1/2`, and
   `λ_C = limsup_n P(O_n ⊆ D_C)^{1/n}`.
   - `P(O_n ⊆ D_C)` is exactly the survival probability up to time `n` of the Markov chain
     `T_i = h_i T_{i−1}` on `(2^C−1)`-point subsets of `D`, with `T_0 = D_C`, killed when `1/2 ∉ T_i`.
   - `λ_C ≤ λ_{C+1} ≤ ‖Q‖ = e^{−Λ_F}`.
   - `λ_{R+2} ≥ λ_R^{ball}`, where `λ_R^{ball}` is the Perron eigenvalue of the walk killed on leaving the
     Cayley ball of radius `R`, and `λ_R^{ball} ↑ ρ(F,μ)`.
   - Hence `F` is amenable ⟺ `sup_C λ_C = 1` ⟺ `Λ_F = 0`.

**What changes.**

- **Quantifier level.** The target `f-dyadic-inverted-orbit-is-subballistic-on-rare-events` quantifies over
  all `ε` and infinitely many `n`. It is now the single number `‖1_E P 1_E‖ = 1`: the Bernoulli shift of `F`
  on `{0,1}^D` has almost invariant sets inside the cylinder `{ω(1/2) = 0}`.
- **Decomposition.** The target splits into band prerequisites `λ_C → 1`. Each is a finite-state
  killed-chain survival question. Any single one can fail, but they cannot all fail unless `F` is
  nonamenable.
- **Correction.** `research/artifacts/hl-f-extensive-amenability-dyadic-2026-09-14.md` asserts that
  bounded-depth confinement costs "an exponential probability with a rate that does not go to 0 with the
  band". By (6) that assertion is *equivalent to the nonamenability of F*, so it cannot be used as an
  obstruction. The multi-scale nesting of bands proposed there is unnecessary: single bands `D_C` with `C → ∞`
  already suffice.
- **Killed class (invariant and step).** Every argument that proves `Λ_F > 0` (hence nonamenability of `F`)
  by bounding the Koopman operator sector by sector on the Walsh decomposition fails. This covers
  `L²(Ω) = ⊕_k ℓ²(P_k(D))`, or any union of levels, followed by the toggle estimate
  `⟨Pf,f⟩ ≤ |⟨f,1⟩|² + ρ_0^+‖f_0‖²` for `f ∈ L²(E)`.
  - **Invariant:** the level top spectra `ρ_k`.
  - **Where it dies:** at the step `⟨Pf_0,f_0⟩ ≤ ρ_k‖f_0‖²`, since `ρ_k = 1` on every level. The Følner sets
    there are the `k`-subsets of the ray `{2^{−1},…,2^{−N}}`, which `x_1` fixes and `x_0` shifts.
  - **Consequence:** a positive exponent must come from the coupling `f̂(A) = f̂(A Δ {x_0})` between levels
    `k` and `k±1` that membership in `L²(E)` imposes. The amenable-stabilizer squeeze of (4) is unavailable
    for `F`, because stabilizers of finite sets of dyadics contain copies of `F`.

**Numerics (bounded runtime, exact dyadic arithmetic, 0 inexact halvings; evidence only).**

Method: Giardinà–Kurchan–Peliti cloning of the chains in (1) and (6), with `μ` uniform on
`{x_0^{±1}, x_1^{±1}}`.

- **F, exponent.** `Λ̂_F`:
  - 0.0577 cumulative at `n = 1000` (`N = 1000`);
  - 0.0462 cumulative at `n = 4000`, with late window rates 0.040–0.043.
- **F, band exponents `−log λ_C`.** Late window rates, `N = 500`, `n = 3000`:

  | C | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
  |---|---|---|---|---|---|---|---|
  | rate | 0.34 | 0.20 | 0.15 | 0.11 | 0.087 | 0.082 | 0.06 |

- **Calibrator with known answer, `PSL_2(Z) ↷ P¹(Q)`.** Here `μ` is uniform on `{S,T,T⁻¹}`, the stabilizers
  are virtually `Z`, and the group is nonamenable. By (4) its exponent is strictly positive, with
  `Λ_PSL ≤ −log p_32^{1/32} = −log 0.87536 = 0.1331` from exact return probabilities.
  - Ball-band late rates decrease steadily: 0.294, 0.143, 0.112, 0.084, 0.075, 0.063, 0.055, 0.052, 0.045
    at band sizes 2, …, 110.
  - `Λ̂_PSL`: cumulative 0.052, late windows 0.047 at `n = 4000`.
  - Its finite-size profile looks like that of `F`.
- **Regular-action calibrators.**
  - `F_2` on itself: estimate 0.298 at `n = 1000`, against the rigorous squeeze `0.0693 ≤ Λ ≤ 0.1438`.
  - `Z³` on itself: estimate 0.191; true value 0 by (3).
  - Lamplighter on itself: estimate 0.120; true value 0 by (3).

**Reading of the numerics.** At accessible sizes, cloning overestimates the exponent by factors of 2 or more.
This is forced by the prefactor `2^{−|B_R|}` in the proof of (3). Separately, the non-extensively-amenable
calibrator shows the same slowly decreasing profile as `F`. So finite-size estimates of `Λ_F` or of `λ_C` cannot
separate "F amenable" from "F not amenable". The value `Λ̂_F ≈ 0.04–0.06` is consistent with both, and lies
below the rigorous ceiling 0.1037.
