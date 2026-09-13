---
rg: 2
id: z3-free-z-embeds-in-gl8z-proof
kind: route
title: Z^k * Z sits in the right-angled Coxeter group (D_inf)^k * D_inf, whose Tits representation is integral and faithful
target: z3-free-z-embeds-in-gl8z
requires: []
---

1. **The Coxeter group.** Let `W` be the right-angled Coxeter group with
   involution generators `s_1, t_1, …, s_(k+1), t_(k+1)`. For `i != j <= k`, each
   of `s_i, t_i` commutes with each of `s_j, t_j`, and there are no other
   relations. The generators `s_(k+1), t_(k+1)` commute with nothing. Then
   `W = P * D`, where `P = ⟨s_i, t_i : i <= k⟩` and `D = ⟨s_(k+1), t_(k+1)⟩ ≅ D_∞`,
   because no relation links the two sets of generators. Also
   `P ≅ D_∞ × ⋯ × D_∞` (`k` factors), because distinct pairs commute and each pair
   `{s_i, t_i}` has no relation.
2. **The free abelian and cyclic pieces.** In `D_∞ = ⟨s, t | s^2, t^2⟩` the
   element `st` has infinite order. So `u_i = s_i t_i` (`i <= k`) generate
   `Z^k <= P`, and `u_(k+1) = s_(k+1)t_(k+1)` generates `Z <= D`.
3. **The free product.** In a free product `A * B`, subgroups `A' <= A` and
   `B' <= B` generate `A' * B'`: an alternating word in nontrivial elements of
   `A'` and `B'` is already a reduced word of `A * B`, so it is nontrivial by the
   normal form theorem. Hence `⟨u_1, …, u_(k+1)⟩ ≅ Z^k * Z <= W`.
4. **Integral faithful representation.** Let `E = Z^(2k+2)` with basis `e_x`, one
   for each generator `x`. Define `B(e_x, e_x) = 1`,
   `B(e_x, e_y) = −cos(π/m_xy)`, which is `0` when `m_xy = 2` and `−1` when
   `m_xy = ∞`, and `σ_x(v) = v − 2B(e_x, v) e_x`.
   - Each `σ_x` is an integral involution with integral inverse.
   - If `B(e_x, e_y) = 0`, then `σ_x` and `σ_y` commute.
   - So `x ↦ σ_x` defines a homomorphism `W → GL_(2k+2)(Z)`.
   - It is faithful: this is Tits's theorem that the geometric representation
     of a Coxeter group is faithful (Bourbaki, *Lie Groups and Lie Algebras*,
     Ch. V §4, no. 4, Corollary 2). Not re-read here; it is the only imported
     input.
5. Composing, `Z^k * Z <= W <= GL_(2k+2)(Z)`, and `k = 3` gives `GL_8(Z)`. ∎
