---
rg: 2
id: char-p-rational-function-fields-in-fp-simple-algebras
kind: claim
title: For every prime p and k >= 1, F_p(t_1..t_k) embeds unitally in an explicit finitely presented simple F_p-algebra with center F_p; hence so does every countable field of characteristic p of finite transcendence degree
distinct_from:
  char-p-rational-function-field-in-fp-simple-algebra: that is the case k = 1 with one Horner register; this handles several variables with nested Horner registers and extends to all countable fields of finite transcendence degree.
  rational-function-fields-embed-in-fp-simple-rings: that is characteristic zero, with the constants Q(t_1..t_k) central; here the center is F_p, and the nonvanishing device is lex-monicity instead of evaluation at integer points.
  field-envelopes-pass-to-algebraic-closures: that is the characteristic-zero transfer to algebraic closures; its ultramatricial mechanism is characteristic-free and is reused here.
  countable-char-zero-fields-embed-in-fp-simple-rings: that is the open statement in characteristic zero; the characteristic-p analogue left open here is the same single field type, infinite transcendence degree.
---

**ESTABLISHED** through `char-p-rational-function-fields-in-fp-simple-algebras-proof` (lane proof,
bh-algebra, not reviewed). No priority is claimed beyond a bounded search.

**The algebra `R_(p,k)`.** Registers: `t_1..t_k`, `P_1..P_k`, and for `2 <= j <= k` a coefficient
register `A_j` and a monomial register `M_j`. Letters, each fixing every register it does not name:

| letter | substitution |
|---|---|
| `v` (vacuum) | `P_j ↦ 1`, `A_j ↦ 0`, `M_j ↦ 1` for all `j` |
| `h_a` (`a ∈ F_p`) | `P_1 ↦ t_1 P_1 + a` |
| `r` | `P_1 ↦ 1` |
| `c_j` (`2 <= j <= k`) | `P_j ↦ P_(j−1)` |
| `H_j` | `P_j ↦ t_j P_j + A_j` |
| `z_j` | `A_j ↦ 0` |
| `e_j` | `A_j ↦ A_j + M_j` |
| `o_j` | `M_j ↦ 1` |
| `μ_(j,i)` (`i < j`) | `M_j ↦ t_i M_j` |
| `m_i` (`1 <= i <= k`) | `t_i ↦ t_i^2` |

`R_(p,k)` is generated over `F_p` by the registers, one resolvent `Γ`, and `s_x, t_x` for every letter
`x`, with relations: Leavitt (L) for the letters; the registers commute pairwise (C); covariance
`Y s_x = s_x σ_x(Y)` for every register `Y` and letter `x` (Cov); and `Γ P_k = 1 = P_k Γ` (Res).
It is finitely presented, over `F_p` and as a ring. For `k = 1` it is, up to the redundant letter
`r`, the algebra of `char-p-rational-function-field-in-fp-simple-algebra`.

**Claim.**
1. `R_(p,k)` is simple with center `F_p`. `F_p(t_1..t_k)` embeds unitally in it, non-centrally,
   together with every free algebra `F_p(t_1..t_k)<x_1, ..., x_m>`.
2. Every finitely generated field `E` of characteristic `p` embeds unitally in `M_d(R_(p,k))` for
   some `d`, where `k = trdeg(E/F_p)`. So do the rings `M_n(E)` and every subring of `M_n(E<x_1..x_m>)`.
   `M_d(R_(p,k))` is finitely presented and simple with center `F_p`.
3. Every countable field `K` of characteristic `p` with finite transcendence degree `k` embeds
   unitally in `R_(p,k) ⊗ L_(F_p)(1,2)`, a finitely presented simple `F_p`-algebra with center `F_p`
   (`R_(p,0) := F_p`). Examples are `F̄_p`, `F̄_p(t)`, and the algebraic closure of
   `F_p(t_1..t_k)`.

**Nonvanishing device.** The resolvent inverts every value of `P_k`. These are exactly the
lex-monic polynomials (leading coefficient `1` for the lexicographic order with
`t_k > ... > t_1`), built by nested Horner steps. Every nonzero polynomial is a nonzero scalar
times a lex-monic one. The squaring letters keep the `t_i` out of the center.

**Consequences and limits.**
- For `p = 2`, every `GL_n(E)` with `E` as in part 2 lies in the unit group of a finitely
  presented central simple `F_2`-algebra. The group gate is the analogue of
  `horner-resolvent-leavitt-tensor-k1-k2-vanish` for `R_(2,k)`.
- Infinite transcendence degree, `F_p(t_1, t_2, ...)`, stays open, as `Q(t_1, t_2, ...)` does in
  characteristic zero.
