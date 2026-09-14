---
rg: 2
id: kazhdan-generators-admit-no-norm-popa-corners
kind: claim
title: In the group von Neumann algebra of an infinite Kazhdan group, the Kazhdan generators have no finite-dimensional norm Popa corners, and every Popa algebra stays norm-far from them
distinct_from:
  kazhdan-group-factor-popa-corners-have-vanishing-trace: that bounds the trace of Popa corners by O((eta+delta)^2) through the spectral gap in L^2(M); this shows that for the exact Kazhdan generators no Popa corner exists at tolerance below eps/4, at any trace, through the coarse bimodule.
  kazhdan-groups-without-fd-reps-avoid-qd-unitary-groups: that forbids exact homomorphic images of Kazhdan groups without finite-dimensional representations in QD algebras; this is a norm-quantitative statement about corners, for every infinite Kazhdan group, residually finite ones included.
artifacts:
  - research/artifacts/sk-popa-lgx-plan-2026-09-13.md
---

**ESTABLISHED (unreviewed, lane sk-popa-lgx, 2026-09-13)** by route `kazhdan-generators-admit-no-norm-popa-corners-proof`.

**Statement.** Let `Γ` be an infinite group with a Kazhdan pair `(S, ε)`, let `M = L(Γ)` with trace `τ`, and let `λ_s ∈ M` be the group unitaries.
- For every nonzero projection `p ∈ M` and every finite-dimensional C*-subalgebra `B ⊆ pMp` with unit `p`,

  `max_{s∈S} ( ‖[λ_s, p]‖ + dist(pλ_sp, B) ) ≥ ε/2`   (operator norm).

**Corollary (Popa algebras are norm-far from Kazhdan generators).** Let `A ⊆ M` be any C*-subalgebra with Popa's local quantization property. For every finite `𝔉 ⊆ A` and `η > 0` there is a nonzero finite-dimensional `B ⊆ A` with unit `e`, `‖[x,e]‖ < η` and `dist(exe, B) < η` for `x ∈ 𝔉`. Weak density and simplicity are not needed. Then

`max_{s∈S} dist(λ_s, A) ≥ ε/6`.

Proof of the corollary:
- Suppose `y_s ∈ A` with `‖y_s − λ_s‖ < θ` for all `s`, and take a Popa corner `(e, B)` for `𝔉 = {y_s}` at tolerance `η`.
- Then `‖[λ_s, e]‖ < η + 2θ` and `dist(eλ_se, B) < η + θ`.
- So the statement gives `2η + 3θ ≥ ε/2` for every `η > 0`, hence `θ ≥ ε/6`.

**Why it matters for Brown's Question 3.** Lemma S (`kazhdan-group-factor-popa-corners-have-vanishing-trace`) lets Popa corners for exact Kazhdan generators exist on corners of trace `O(η²)`. The statement here shows that they do not exist at all once the tolerance is below `ε/4`. The proof normalizes a vector of the coarse bimodule, so the trace of the corner never enters. A weakly dense Popa algebra in a property (T) group factor therefore approximates the Kazhdan generators only in 2-norm, never within `ε/6` in norm. See `orthogonal-popa-corners-for-kazhdan-approximants-small-trace` for the quantitative 2-norm version.

**General (T) factors (remark, not claimed).** For a II_1 factor with property (T) in the Connes–Jones sense, with critical pair `(F, ε)` (Bull. London Math. Soc. 17 (1985); recalled, locator not checked), the same proof gives `max_{x∈F}(‖[x,p]‖ + dist(pxp,B)) ≥ ε/2`, because the coarse bimodule of a diffuse algebra has no nonzero central vectors.

**Model tests.**
- **Finite `Γ`:** `p = 1` and `B = M = L(Γ)` give commutators `0`, so the statement fails. The proof uses that the conjugation representation on `ℓ²(Γ×Γ)` has no invariant vectors, which needs `Γ` infinite.
- **`Γ = Z`, no Kazhdan pair:** `L(Z) = L^∞(T)`, and `λ_1 = z` is within any `η` in norm of a step function spanning a finite-dimensional subalgebra, with `p = 1`. The conclusion fails, as it should.
- **`Γ = SL_3(Z)`:** residually finite with property (T). The statement forbids norm Popa corners for `λ(S)` although `Γ` has many finite quotients. Finite quotients give finite-dimensional representations of `C*(Γ)`, not of subalgebras of `L(Γ)`, so there is no conflict.
