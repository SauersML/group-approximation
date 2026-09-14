---
rg: 2
id: jacobson-half-line-group-contains-finitary-sl-proof
kind: route
title: Commute X with the four generators, climb the window by conjugation and commutators, then use simplicity and the symbol
target: jacobson-half-line-group-contains-finitary-sl
requires:
  - five-transvection-group-acts-on-jacobson-half-line
  - four-transvection-units-have-a-weakly-finite-symbol-image
artifacts:
  - experiments/gottschalk-transvections/sl_fin_ladder_check.py
---

## Why sufficient

Write `[g, h] = g h g^(-1) h^(-1)` and `E_qp` for `I + E_qp in Γ_V`. Since `(I + E_qp)^2 = I + 2E_qp`, this
covers every `λ`. Four tools:
- **(F1)** If `x^2 = n^2 = 0`, then `[I + x, I + n] = I + xn - nx + nxn - xnx + xnxn`.
- **(F2)** `g (I + E_qp) g^(-1) = I + (g e_q) ⊗ (e_p^* g^(-1))`, and `e_p^* (I + N)^(-1) = e_p^* - e_p^* N`.
- **(F3)** `[I + E_ab, I + E_bc] = I + E_ac` for distinct `a, b, c`.
- **(F4)** Two transvections of `F_3^2` with distinct centres generate `SL_2(F_3)`. A proper subgroup of `SL_2(F_3)`
  has order 1, 2, 3, 4, 6 or 8, so it has at most one subgroup of order 3. So `I + E_ab` and a transvection
  `I + v ⊗ φ` supported on `{a, b}`, with centre `v` not a multiple of `e_a`, give `E_ba`.

The facts used: `N_A` sends `e_(2n+1)` to `e_(2n)`, so `A e_q = e_q + [q odd] e_(q-1)` and
`e_p^* N_A = [p even] e_(p+1)^*`. Similarly:
- `B e_q = e_q + [q even] e_(q+1)`, and `e_0^* N_B = 0`;
- `C e_q = e_q + [q even, q >= 2] e_(q-1)`, and `e_p^* N_C = [p odd] e_(p+1)^*`;
- `D e_q = e_q + [q odd] e_(q+1)`, and `e_0^* N_D = 0`.

1. **Commutators with X** (F1, with `x = E_31`).
   - `[X, A] = I - E_21`, since `xn = 0` and `nx = E_21`.
   - `[X, B] = I + E_30`, since `xn = E_30` (`N_B e_0 = e_1`) and `nx = 0`.
   - `[X, C] = I + E_32`, since `xn = E_32`.
   - `[X, D] = I - E_41`, since `nx = E_41`.
   - In each case the cubic and quartic terms vanish.
2. **The window {0, ..., 4}.**
   - `C E_21 C^(-1) = I + (e_2 + e_1) ⊗ (e_1^* - e_2^*)`, so F4 gives `E_12`.
   - `A E_32 A^(-1) = I + (e_3 + e_2) ⊗ (e_2^* - e_3^*)`, so F4 gives `E_23`.
   - `E_20 = [E_23, E_30]`.
   - `C E_20 C^(-1) = (I + E_20)(I + E_10)` gives `E_10`.
   - `A E_10 A^(-1) = I + (e_1 + e_0) ⊗ (e_0^* - e_1^*)`, so F4 gives `E_01`.
   - By F3: `E_02 = [E_01, E_12]`, `E_13 = [E_12, E_23]`, `E_03 = [E_01, E_13]`, `E_40 = [E_41, E_10]`,
     `E_42 = [E_41, E_12]` and `E_43 = [E_42, E_23]`.
   - `C E_03 C^(-1) = (I + E_03)(I - E_04)` gives `E_04`. Then `E_q4 = [E_q0, E_04]` for `q = 1, 2, 3`.
   - Every `E_qp` with `p != q <= 4` is now in `Γ_V`.
3. **Induction.** Suppose every `E_qp` with `p != q <= K` is in `Γ_V`, for some `K >= 4`.
   - **Source `K+1`.** For `K` even, `A E_0K A^(-1) = (I + E_0K)(I - E_(0,K+1))`. For `K` odd, the same holds with
     `C`. This uses `A e_0 = C e_0 = e_0`.
   - **Target `K+1`.** For `K` even, `B E_K0 B^(-1) = (I + E_K0)(I + E_(K+1,0))`. For `K` odd, the same holds with
     `D`.
   - **The rest.** `E_(q,K+1) = [E_q0, E_(0,K+1)]` and `E_(K+1,p) = [E_(K+1,0), E_0p]`.

   The products split because the two rank-one terms annihilate each other.
4. **SL_fin and simplicity.** Elementary transvections generate `SL_M(F_3)` on each window, which gives item 1.
   - **Normality.** `GL_fin(V) = ker π` is normal in `GL_2(J)`. `SL_fin(V)` is its commutator subgroup, so it is
     characteristic in `GL_fin(V)` and normal in `Γ_V`.
   - **Simplicity.** Take a nontrivial normal subgroup `N` and `1 != g in N ∩ SL_M`. For `M' >= max(M + 1, 3)`, `g` is
     not scalar in `SL_(M')`. So `N ∩ SL_(M')` is a noncentral normal subgroup of `SL_(M')(F_3)`, and equals
     `SL_(M')(F_3)`. So `N = SL_fin(V)`.
   - **Consequences.** A homomorphism to a finite group, or to the units of a finite-dimensional algebra (a finite
     group), has a kernel of finite index in the infinite simple group `SL_fin(V)`. So it kills `SL_fin(V)`, hence `X`
     and `D`.
5. **The symbol preimage.**
   - `Γ_V <= GL_2(J)`, and the generator symbols are unipotent, so `Γ_V <= 𝒯`.
   - The symbols of `A, B, C, D` are those of `Φ(S4)` in `four-transvection-units-have-a-weakly-finite-symbol-image`,
     under `s_0 -> S -> ζ` and `t_0 -> T -> ζ^(-1)`. So `π(Γ_V) = SL_2(F_3[ζ, ζ^(-1)]) = π(𝒯)`.
   - Hence `𝒯 = Γ_V GL_fin(V)`, with `GL_fin(V)` normal in `𝒯`. So
     `[𝒯 : Γ_V] = [GL_fin(V) : Γ_V ∩ GL_fin(V)] <= [GL_fin(V) : SL_fin(V)] = 2`.
