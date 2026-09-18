---
rg: 2
id: char-p-rational-function-field-in-fp-simple-algebra
kind: claim
title: For every prime p, the rational function field F_p(t) embeds unitally in an explicit finitely presented simple F_p-algebra whose center is F_p
distinct_from:
  rational-function-fields-embed-in-fp-simple-rings: that is characteristic zero, where the constants Q(t_1..t_k) are central and the resolvent value N + 1 + Σ (t_i − c_i) P_i is kept nonzero by evaluating at integer points; this is characteristic p, where that value can vanish, the resolvent inverts Horner registers instead, and a squaring letter makes t non-central so that the center is only F_p.
  rational-function-field-embeds-in-binary-leavitt-algebra: that asks for F_2(t) inside the one fixed algebra L_(F_2)(1,2); this builds a different finitely presented simple F_2-algebra containing F_2(t), with no claim about L_(F_2)(1,2).
  field-representable-algebras-have-fp-simple-envelopes: that embeds finitely generated subalgebras of matrices over fields; this embeds the whole field F_p(t), which is not finitely generated.
---

**ESTABLISHED** through `char-p-rational-function-field-in-fp-simple-algebra-proof`
(lane proof, bh-algebra, not reviewed). No priority is claimed beyond a bounded search: the
graph has the characteristic-zero construction but no finitely presented simple algebra over a
finite field containing a transcendental field, and a bounded arXiv search found none.

**The algebra.** Fix a prime `p`. The alphabet has `d = p + 2` letters: Horner letters `h_a`
(`a ∈ F_p`), a vacuum letter `v` and a squaring letter `m`. Let `R_p` be the unital
`F_p`-algebra with generators `t, P, Γ` and `s_x, t_x` (`x` a letter), and relations

- (L) `t_x s_y = δ_(xy)` and `Σ_x s_x t_x = 1`;
- (C) `t P = P t`;
- (Cov) `t s_x = s_x σ_x(t)` and `P s_x = s_x σ_x(P)` for every letter `x`, where

  | letter | `σ_x(t)` | `σ_x(P)` |
  |---|---|---|
  | `h_a` | `t` | `t P + a` |
  | `v` | `t` | `1` |
  | `m` | `t^2` | `P` |

- (Res) `Γ P = 1 = P Γ`.

That is `3 + 2d` generators and `d^2 + 2d + 4` relations. For `p = 2`: 11 generators, 28
relations.

**Claim.**
1. `R_p` is simple, and its center is `F_p`.
2. `F_p[t] ⊆ R_p` extends to a unital embedding `F_p(t) -> R_p`. The inverse of a monic
   `f` is explicit: if `f = t^r + a_1 t^(r−1) + ... + a_r`, then
   `f^(−1) = t_v t_(h_(a_1)) ... t_(h_(a_r)) Γ s_(h_(a_r)) ... s_(h_(a_1)) s_v`.
3. For every `m >= 1` the free algebra `F_p(t)<x_1, ..., x_m>` embeds in `R_p`.
4. `R_p` is also finitely presented as a ring (add `p = 0`).

**Why the design.**
- *Nonvanishing.* In characteristic `p` the characteristic-zero device fails: `N + 1` can be
  `0`. Every nonzero polynomial is a nonzero scalar times a monic one, and the Horner letters
  realize exactly the monic polynomials as vacuum values of `P`.
- *Small center.* If `t` commuted with every letter, `F_p(t)` would be central, as `Q(t)` is in
  the characteristic-zero host. The squaring letter `m` moves `t`. The only elements of `F_p(t)`
  fixed by `t ↦ t^2` are constants, so the center is `F_p`. For the Leavitt tensor host of
  groups (`leavitt-tensor-elementary-host-criterion`, `central-simple-leavitt-tensor-unit-groups-are-simple`)
  this makes `R_2` a finitely presented *central* simple `F_2`-algebra.

**Consequence for groups (p = 2).** `GL_n(F_2(t)) <= GL_n(R_2)`. The route
`gl-n-f2t-bh-via-horner-resolvent-leavitt-tensor` reduces `gl-n-f2t-embeds-in-fp-simple-group`
to the single K-theory gate `horner-resolvent-leavitt-tensor-k1-k2-vanish`.

**Open.** The multivariable case `F_p(t_1, ..., t_k)` for `k >= 2`, where not every nonzero
polynomial is a scalar multiple of a Horner value in one register.
