---
rg: 2
id: free-centre-by-metabelian-linearity-via-gamma-seven-quotient
kind: route
title: The corner representation kills only the torsion, and the torsion survives modulo gamma_7, so C_n embeds in a product of two linear groups
target: free-centre-by-metabelian-groups-are-linear
requires:
  - free-centre-by-metabelian-corner-kernel-is-the-torsion
  - gupta-torsion-element-survives-modulo-gamma-seven
---

Write `T_n` for the torsion subgroup of `C_n` and `ρ_n` for the corner representation.

1. **The kernel of the product.** The kernel of `C_n -> ρ_n(C_n) × C_n/γ_7(C_n)` is
   `ker ρ_n ∩ γ_7(C_n) = T_n ∩ γ_7(C_n)`, by `free-centre-by-metabelian-corner-kernel-is-the-torsion`.
2. **n ≤ 3.** `T_n = 0` and there is nothing to prove.
3. **n = 4.** `T_4` is cyclic, and its unique involution is Gupta's element `u_6`. Every
   nontrivial subgroup of a cyclic group of even order contains that involution. By
   `gupta-torsion-element-survives-modulo-gamma-seven`, `u_6 ∉ γ_7(C_4)`. Hence
   `T_4 ∩ γ_7(C_4) = 1`.
4. **n ≥ 5.** Let `1 ≠ τ ∈ T_n ∩ γ_7(C_n)`.
   - The retractions `r_S: C_n -> C_4`, for 4-subsets `S`, are jointly injective on
     `T_n`. So `r_S(τ) ≠ 1` for some `S`.
   - Retractions map `γ_7` into `γ_7`, so `1 ≠ r_S(τ) ∈ T_4 ∩ γ_7(C_4)`. This contradicts
     step 3.
5. **Linearity.** Both factors are linear in characteristic zero:
   - `ρ_n(C_n) ⊆ GL_(2n+1)(Z[x_i^(±1)])`;
   - `C_n/γ_7(C_n)` is finitely generated nilpotent, hence polycyclic, hence embeds in
     some `GL_m(Z)` (Auslander–Swan).

   Block-diagonally, `C_n ↪ GL_(2n+1+m)(Q(x_1, …, x_n))`.
6. **Residual properties.** Residual finiteness follows from linearity (Mal'cev).
   For residual nilpotence, use Hurley's representation `θ: f_i ↦ 1 + x_i` into the units
   of the graded power-series ring `P` (Gupta–Levin p. 259). It has `Ker θ = faf` on `ZF`.
   - `θ(γ_c(F)) ⊆ 1 + P_(>=c)` and `∩_c (1 + P_(>=c)) = 1`, so
     `∩_c γ_c(C_n) ⊆ ker(θ on C_n)`.
   - By Gupta–Levin Lemma 2.2(i), `ker(θ on C_n) = K_6(F)[F'',F]/[F'',F]`. By Lemma
     2.2(iii) this has exponent 2, so it lies in `T_n`.
   - With step 4, `∩_c γ_c(C_n) ⊆ T_n ∩ γ_7(C_n) = 1`. ∎

## Attempts

- **Verification note (bh-verify-cbm, 2026-09-18; report `research/artifacts/gq-bh-bh-verify-cbm-report.md`).**
  - **The flaw.** In step 3, "every nontrivial subgroup of a cyclic group of even order contains that
    involution" is false (`Z/3 ≤ Z/6`). The step needs `|T_4|` to be a power of 2. Kuz'min's `d = 2` supplies
    that, but it was cited, not read.
  - **Repair without Kuz'min.** It uses only Gupta–Levin Lemma 2.2(i),(iii) and Lemma 4.4, read at source.
    - `∩_c γ_c(C_n) ⊆ ker(θ|C_n) = K_6[F'', F]/[F'', F]`, which is elementary abelian of exponent 2 and lies in `T_n`.
    - In the cyclic group `T_4` this forces `ker θ ∩ T_4 = {1, u_6}`.
    - Since `u_6 ∉ γ_7`, we get `T_4 ∩ ∩_c γ_c = 1`, and retractions give `∩_c γ_c(C_n) = 1`.
    - `T_n` is finite, so `T_n ∩ γ_c(C_n) = 1` for some finite `c ≥ 7`. Then `C_n ↪ ρ_n(C_n) × C_n/γ_c(C_n)`.
  - **Effect.** The target theorem (linear, residually nilpotent, residually finite, in `B_A`) holds either way.
    The specific bound `c = 7` needs `d = 2`.
