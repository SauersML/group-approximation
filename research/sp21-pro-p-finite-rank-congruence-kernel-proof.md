---
rg: 2
id: sp21-pro-p-finite-rank-congruence-kernel-proof
kind: route
title: Kill the radical by superrigidity and vanishing cohomology, then force the kernel ideal to act trivially on itself
target: sp21-pro-p-finite-rank-iff-finite-pro-p-congruence-kernel
requires: []
artifacts:
  - research/artifacts/hyperbolic-rf-pro-p-2026-09-12.md
---

**Imported inputs (statements only; the sources were not re-read here).**
- **(L)** Lazard and Lubotzky–Mann: a finitely generated pro-p group has finite
  rank iff it has an open uniform subgroup. For uniform `U` with Lie algebra `𝔭`,
  `Ad(exp X) = exp(ad X)` for small `X`.
- **(SR)** Margulis-form superrigidity for finite-index subgroups of `Γ`, as stated
  in `sp21-bounded-rank-simple-quotients-almost-all-congruence-proof`.
- **(V)** Raghunathan's vanishing theorem together with property (T): `H^1` of a
  finite-index subgroup vanishes with coefficients in any finite-dimensional
  algebraic representation of `Res_(k/Q) G`, over any characteristic-`0` field.
- **(T)** Kostant: every finite-index subgroup has finite abelianization.

**Proof.**

**(⇐)** A finite extension of the p-adic analytic group `Δ̄_p` has finite rank.

**(⇒)** Let `P = Δ̂_p` have finite rank. Take an open uniform `U` with Lie algebra
`𝔭`, and put `Δ₀ = Δ ∩ U`, which is dense in `U`.

1. **`𝔭` is perfect.** Otherwise `U^ab` is infinite and `Δ₀^ab` is infinite,
   contradicting (T).
2. **`𝔭` is semisimple.**
   - The radical `𝔯` is nilpotent on `𝔭`. If `ad 𝔯 = 0` then `𝔯` is central and
     `𝔯 ⊆ [𝔭,𝔭] ⊆ 𝔰`, so `𝔯 = 0`.
   - Otherwise the Zariski closure `H° = S ⋉ R_u` of `Ad(Δ₀)` has `R_u != 1`.
     Modulo `[R_u,R_u]`, the `R_u`-part is a cocycle `ū ∈ Z^1(Δ₁, V)`, where
     `V = R_u/[R_u,R_u] != 0` and `Δ₁` acts through `s: Δ₁ -> S` with
     Zariski-dense image.
   - (SR), applied factor by factor over `Q̄_p` and lifted through the simply
     connected `G`, makes `V` algebraic for `Res_(k/Q) G` on a finite-index subgroup.
   - (V) and injectivity of restriction give `H^1(Δ₁, V) = 0`. So `ū` is a
     coboundary, and a conjugate of `Ad(Δ₁)` lies in `S ⋉ [R_u,R_u]`,
     contradicting Zariski density.
3. **The kernel ideal is zero.**
   - Let `𝔫 = Lie(ker π_Δ ∩ U)`, a semisimple ideal.
   - The adjoint image of a finite-index `Δ₃` on `𝔫` is Zariski dense in `Int(𝔫)`.
   - By (SR), `Ad|_𝔫 = (τ_i σ_i)_i`, and each `σ_i: k -> Q̄_p` is continuous for a
     place `v_i | p`. So `Ad|_𝔫 = F ∘ π_Δ` on `Δ₃`, with `F` continuous.
   - By density both sides agree on the open closure `W₃` of `Δ₃`.
   - For `w = exp X ∈ ker π_Δ ∩ W₃` this gives `exp(ad X|_𝔫) = id`, so `𝔫` is
     abelian, hence `0`.
   - So `ker π_Δ` is finite. ∎
