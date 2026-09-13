---
rg: 2
id: sl3z-cocompact-microstates-carry-flat-lambda-labels-proof
kind: route
title: Compact lifts bound all conjugations, so approximate label identities in the discrete Λ are exact; norm drift prices finite orbits
target: sl3z-cocompact-microstates-carry-flat-lambda-labels
requires:
  - sl3-norm-drift-excludes-finite-almost-invariant-configs
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-holonomy-drift-2026-09-13.md
---

Full proof: Sections 1 and 2 (Lemmas 1.1--1.2, Definition 1.3, Corollary 2.3) of the artifact.

1. **Constants.** Put `K = S^(<=L)F ∪ F`. Let `C_1` bound conjugation by `K^(±1)` near `1`, put
   `r_Λ = min_(λ != 1) d(λ,1)`, and `ε_0 = min(1, r_Λ/(2LC_1^2))`.
2. **Uniqueness.** If `λ, λ'` both label `(v,s)`, then with `x = s g_v ∈ K`,
   `d(1, xλ'λ^(−1)x^(−1)) < 2ε`, so `d(λ'λ^(−1), 1) < 2C_1ε < r_Λ`.
3. **Flatness.** Write `g_(v_i) = e_i s_i g_(v_(i−1)) λ_i` with `d(e_i,1) < ε`. Around a relator
   `s_m···s_1 = 1` this gives `g = E g λ_1···λ_m`, where `E` is a product of `m <= L` conjugates
   `p_i e_i p_i^(−1)` with `p_i ∈ K`. So `d(λ_1···λ_m, 1) <= LC_1^2ε < r_Λ`.
4. **Labelled system.** Bijectivity and commutation are immediate. By right-invariance,
   `d(Φ(σ̃_sω), sΦ(ω)) = d(g_(σ_s v), s g_v λ(v,s))`, and on bad pairs a minimizing label gives at most
   `diam(X)`. For an honest action with all pairs good, flatness makes the label product along a word
   depend only on the group element. Its inverse restricted to `Γ_v` is a homomorphism, and the
   stabilizer of `(v,μ)` is its kernel.
5. **Defects.** Apply `sl3-norm-drift-excludes-finite-almost-invariant-configs` to `σ̃|_O` with
   `η = η(ε)` and `B = B(diam X)`. This gives `θ >= (κ/12 − η(ε))/B` whenever `η(ε) < κ/12`. ∎
