---
rg: 2
id: fpbs-strongly-ergodic-actions-have-fold-seed-floor-proof
kind: route
title: Stop the fold closure rounds at half measure; each derived point uses up its own triple inside the crossing set, so seeds pay its a,b-boundary, which the Markov gap bounds below
target: fpbs-strongly-ergodic-actions-have-fold-seed-floor
requires:
  - kesten-amenable-stabilizer-uniform-gap
artifacts:
  - research/artifacts/fpbs-spectral-fold-seed-floor-2026-09-18.md
  - experiments/fpbs-z3-overgroup-2026-09-17/spectral_check.py
  - experiments/fpbs-z3-overgroup-2026-09-17/spectral_check_out.txt
---

The complete proof is §1 to §3 of the artifact. Imports: Kechris' definition of
weak containment; `kesten-amenable-stabilizer-uniform-gap` with `H = {1}`
(`rho < 1`); for the numerical value only, Kesten's formula `rho(F_k) =
√(2k−1)/k` (Kesten, Trans. AMS 92 (1959), Theorem 3).

1. **Rounds.** `C_0 = A`, and `C_k` adds every point that fills one position
   of a triple whose two other positions lie in `C_{k-1}`. Then
   `cl(A) = ∪ C_k`.
2. **Derivation map (Lemma 1.1).** Let `C_{k-1} ⊆ I ⊆ C_k`. For `z ∈ I \ A`,
   pick measurably a derivation triple `T_{w(z)}` with
   `w(z) ∈ {z, a^{-1}z, b^{-1}z}`. Its other positions entered earlier, so
   `T_{w(z)} ⊆ I`. The map is injective: a second point derived by the same
   triple would already be in an earlier round. It is also piecewise
   measure-preserving. So `μ(I ∩ a^{-1}I ∩ b^{-1}I) ≥ μ(I) − μ(A)`.
3. **Crossing (Proposition 1.2).** If `μ(A) < 1/2` and `cl(A)` is conull, some
   round crosses `1/2`. Non-atomicity gives `I` with `μ(I) = 1/2` between two
   rounds. Then `μ(A) ≥ μ(I \ (a^{-1}I ∩ b^{-1}I)) ≥ max_s μ(IΔsI)/2`.
4. **Spectral step (§2).** With `f = 1_I − 1/2`:
   `μ(IΔaI) + μ(IΔbI) = 1 − 4<Mf,f> ≥ 1 − rho_X`.
5. **Consequences (§3).**
   - Strong ergodicity rules out measure-1/2 almost invariant sets.
   - `kappa` is antitone under weak containment, by Kechris' definition with
     one set.
   - On a Bernoulli shift, and on its pullback along any injective
     endomorphism such as `φ^j`, `L^2_0` is a multiple of `λ_L`, since
     finite-support basis tensors have trivial stabilizers.
   - Theorem B transfers the bound to graphings.
6. **Finite check.** `spectral_check.py` verifies
   `r(Q) ≥ kappa'(Q) ≥ n(1 − λ_2)/4` exhaustively on random Schreier graphs
   with `n = 12, 16`.
