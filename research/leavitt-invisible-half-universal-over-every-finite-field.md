---
rg: 2
id: leavitt-invisible-half-universal-over-every-finite-field
kind: claim
title: Over every finite field, every Kaplansky pair over Leavitt units transfers into an evaluation-invisible kernel corner
distinct_from:
  leavitt-unit-group-algebra-embeds-in-kernel-corner: that is the binary level-one case, cut by 1 + g + g^2 in F_2[GL_2(F_2)]; this is the criterion for every field, every Leavitt type (1,d) and every level, together with the existence of a suitable cut over every finite field.
  ternary-anti-central-failures-transfer-into-kernel-corners: that embeds the ternary anti-central summand with a level-two Klein idempotent; this gives the general criterion, which also covers the whole ternary group algebra, and proves that level one is empty over F_3.
artifacts:
  - research/artifacts/leavitt-invisible-corner-transfer-2026-09-12.md
---

Let `F` be a field and `R` a unital `F`-algebra with a Leavitt family of type `(1,d)`,
`d >= 2`. Put `Q = R^x`, `S = F[Q]`, `pi : S -> R` the evaluation, `K = ker pi` and
`K^+ = F 1 + K`. For `n = d^k` let `Theta_n : M_n(R) -> R` be the word isomorphism
`(a_(gamma, gamma')) -> sum S[gamma] a_(gamma, gamma') T[gamma']`, and `delta_n(q) = Theta_n(q I_n)`.

**Criterion.** Suppose `H <= GL_n(F)` contains no scalar matrix except `I_n`, and
`e = sum_h e_h h` is a nonzero idempotent of `F[H]` killed by the natural representation. Then:
* `z = sum_h e_h [Theta_n(h)]` is an idempotent of `K`;
* `mu(a) = delta_(n*)(a) z` is an injective ring homomorphism `S -> zSz` with `mu(1) = z`;
* every pair `b a = 1 != a b` in `S` becomes the invisible pair `(1 - z) + mu(a)`,
  `(1 - z) + mu(b)`;
* `S`, `K^+` and `zSz` are directly finite together, at every matrix size.

**Existence.** For `R = L_(F_q)(1,d)` a suitable `(H, e)` exists for every prime power `q` and
every `d >= 2`.
* **Level one, `(q, d) != (3, 2)`:** the averaging idempotent of a torus element of odd prime
  order. For `d = 2` it comes from an odd prime divisor of `q - 1` or `q + 1`. For `d >= 3` it
  comes from a Zsigmondy primitive prime divisor of `q^d - 1`, with `diag(g, g, g)` for `(2, 6)`.
* **Level two, `(3, 2)`:** the Klein group `<diag(1,1,-1,-1), diag(-1,-1,1,-1)>` from
  `gk-l3-kernel`, or an element of order `5` in `GL_4(F_3)`.

At level one over `F_3`, no scalar-free subgroup of `GL_2(F_3)` carries any nonzero idempotent
killed by the natural representation. So passing to level two is necessary there.

**Consequence.** For every finite field `F_q` and every `d >= 2`, direct finiteness of
`F_q[L_(F_q)(1,d)^x]` is equivalent to direct finiteness of the unitized evaluation kernel, and
to that of a single kernel corner. On the existence side, the evaluation-invisible form of a
Kaplansky failure is universal over every finite field. None of this decides direct finiteness.

Independent re-derivation requested from `gk-vf-linear`.
