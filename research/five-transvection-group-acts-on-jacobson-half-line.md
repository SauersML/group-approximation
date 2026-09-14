---
rg: 2
id: five-transvection-group-acts-on-jacobson-half-line
kind: claim
title: The five-transvection group preserves the words sigma 0^n 1^∞ and acts on them through GL_2 of the ternary Jacobson algebra, keeping the eight defect elements distinct
distinct_from:
  four-transvection-units-have-a-weakly-finite-symbol-image: that puts <S4> inside EL_2 of the Jacobson algebra through the code-(0,1) frame and uses its symbol, which sends x_23(1) to 1; this realizes all of Γ_5, x_23(1) included, by half-line operators on an invariant subspace, where x_23(1) is a nontrivial finitary transvection and the eight elements z^e x_23(1)^a x_12(1)^b stay distinct.
  jacobson-elementary-subgroups-are-locally-finite-by-linear: that gives the structure of every subgroup of EL_n over a finite-field Jacobson algebra; this produces one homomorphism from Γ_5 into GL_2 of the ternary Jacobson algebra that keeps the two-root defect visible.
---

**ESTABLISHED** (route `five-transvection-group-acts-on-jacobson-half-line-proof`; lane `gk3-transvections`,
2026-09-14; not yet independently re-derived).

**Setting.** As in `four-transvections-and-x23-force-defect-vanishing`: `R = L_(F_3)(1,2)`, `z = -1`,
`T_(σ,κ) = 1 + s_σ t_κ`, `x_23(1) = 1 + s_10 t_11`, `x_12(1) = 1 + s_0 t_10` and
`Γ_5 = <T_(0,1), T_(1,0), T_(1,00), T_(00,1), x_23(1)>`.
- `R` acts on `F_3[Ω]`, `Ω = {0,1}^N`, by `s_i w = iw` and `t_i(jw) = δ_ij w`.
- `J = F_3<S, T | TS = 1>` acts faithfully on `F_3[N]` by `S e_n = e_(n+1)`, `T e_n = e_(n-1)`, `T e_0 = 0`.
  Put `e = 1 - ST = E_00`.

**Statement.**
1. `V = span{w_(σ,n) = σ 0^n 1^∞ : σ in {0,1}, n >= 0}` is invariant under every generator of `Γ_5` and its inverse.
   So restriction is a homomorphism `ρ_V : Γ_5 -> GL(V)`.
2. With `V = V_0 ⊕ V_1` and `e_n <-> w_(σ,n)` in each copy, `ρ_V` sends the generators to
   `E_01(1)`, `E_10(1)`, `E_10(T)`, `E_01(S)` and `diag(1, 1 + S e)`, so `Γ_V := ρ_V(Γ_5) <= GL_2(J)`.
   Also `ρ_V(z) = -I` and `ρ_V(x_12(1)) = E_01(T)`.
3. The eight elements `z^e x_23(1)^a x_12(1)^b` with `e, a, b in {0,1}` have distinct images under `ρ_V`.
4. The symbol `S -> ζ`, `T -> ζ^(-1)` maps `Γ_V` into `SL_2(F_3[ζ, ζ^(-1)])` with locally finite kernel, contained in
   `I + M_2(M_∞(F_3))`. The image of `x_23(1)` lies in that kernel.

**Consequences.**
- **Refuter.** A weakly finite model of `Γ_V` with `-I -> -1` and nonzero defect refutes
  `four-transvections-and-x23-force-defect-vanishing`, since composing with `ρ_V` keeps `z -> -1` and the defect. In
  particular soficity of `Γ_V` (`jacobson-image-of-five-transvection-group-is-sofic`) does, through route
  `weakly-finite-nonzero-defect-via-sofic-jacobson-image`. No Leavitt relation beyond the half-line is needed.
- **Cost of the vanishing claim.** If `four-transvections-and-x23-force-defect-vanishing` holds, `Γ_V` is not sofic. `Γ_V` is
  locally finite by a subgroup of `SL_2(F_3[ζ, ζ^(-1)])`. That group is discrete in
  `SL_2(F_3((ζ))) x SL_2(F_3((ζ^(-1))))` and acts properly on the product of the two Bruhat–Tits trees, so it has the
  Haagerup property and no infinite subgroup with property (T). A proof of the vanishing claim must therefore show that
  a locally-finite-by-Haagerup group is not sofic, and arguments that use property (T) of the quotient do not reach it.
