---
rg: 2
id: one-sided-free-hnn-positive-l2-betti-proof
kind: route
title: Euler--Poincare on the standard 2-complex gives b_2 >= chi; ell^2 2-cycles on a 2-dimensional host are subgroup-independent, so b_2 = 0 on the host kills every subgroup
target: one-sided-free-hnn-inputs-have-positive-second-l2-betti
requires: []
---

The argument is the "Proof" section of `one-sided-free-hnn-inputs-have-positive-second-l2-betti`.
It uses no graph prerequisites, only the literature imports listed there. The steps are:

1. **Input side.**
   - The double mapping cylinder of `R_A ⇉ R` is a finite aspherical 2-complex with `π_1 = G`, and
     `χ = rk A - rk F`.
   - L2 Euler--Poincaré, together with `b_0^(2) = 0` for infinite `G`, gives
     `b_2^(2)(G) = χ + b_1^(2)(G) >= χ`.
   - Schreier's formula `rk A = m(r-1) + 1` gives `χ = (m-1)(r-1)` in the one-sided case.
2. **Subgroup lemma.**
   - On the universal cover `X` of a finite 2-dimensional `K(K,1)`, `b_2^(2)(K) = 0` means
     `ker ∂_2 = 0` on `ℓ²C_2(X)`, by faithfulness of the von Neumann dimension.
   - For `H <= K`, compute `b_2^(2)(H)` in Lück's extended sense on the free `H`-resolution
     `C_*(X)`. Evaluation at `δ_e` injects `ker(id ⊗ ∂_2)` on `⊕_Σ N(H)` into `ker ∂_2` on
     `ℓ²C_2(X)`: finitely many orbit representatives, with square-summable coefficients.
   - So `ker(id ⊗ ∂_2) = 0` and `b_2^(2)(H) = 0`.
3. **Host vanishing.**
   - (H1) Lück, Thm 1.39: the mapping torus of a cellular self-map is L2-acyclic.
   - (H2) Lyndon asphericity and Dicks--Linnell.
   - (H3) L2 Mayer--Vietoris: `b_2 <= Σ_v b_2(K_v) + Σ_e b_1(Z) = 0`.
4. **3-manifolds.** Scott's core, the orientation cover, and Kneser--Milnor. Each prime factor with
   infinite `π_1` is `S^1 × S^2`, or is aspherical with `χ = χ(∂)/2 <= 0`. So
   `χ(π_1 N) = Σ χ_i - (k-1) <= 0 < χ(G')`.
5. **Instance.** Stallings folding (`experiments/l2-one-sided-hnn-2026-09-17/stallings_check.out`)
   gives ranks `3, 3` and indices `2, ∞`. `BS(1,2) = <t, y>` is not residually nilpotent.
