---
rg: 2
id: leavitt-subalgebra-linear-groups-proof
kind: route
title: Identify M_n(R) with R through an n-leaf complete prefix code and restrict to the subalgebra
target: leavitt-subalgebra-linear-groups-satisfy-boone-higman
requires:
  - leavitt-unit-group-finitely-presented
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

Write `R = F_2<s_0,s_1,t_0,t_1 | t_a s_b = delta_ab, s_0 t_0 + s_1 t_1 = 1>`,
and for a binary word `mu = a_1...a_k` put `s_mu = s_(a_1)...s_(a_k)` and
`t_mu = t_(a_k)...t_(a_1)`.

**Prefix-code matrix units.** For `n >= 2` take the complete prefix code
`mu_1 = 0, mu_2 = 10, ..., mu_(n-1) = 1^(n-2)0, mu_n = 1^(n-1)`. Letterwise
`t_a s_b = delta_ab` gives `t_(mu_i) s_(mu_j) = delta_ij`, since distinct code
words are incomparable, and induction on `n` with `s_0 t_0 + s_1 t_1 = 1` gives
`sum_i s_(mu_i) t_(mu_i) = 1`. Define

```text
Phi: M_n(R) -> R,   (a_ij) |-> sum_(i,j) s_(mu_i) a_ij t_(mu_j),
Psi: R -> M_n(R),   r |-> (t_(mu_i) r s_(mu_j))_(i,j).
```

Then `Phi(a)Phi(b) = Phi(ab)` because `t_(mu_j) s_(mu_k) = delta_jk`,
`Phi(1) = sum_i s_(mu_i) t_(mu_i) = 1`, `Psi(Phi(a)) = a`, and
`Phi(Psi(r)) = (sum_i s_(mu_i) t_(mu_i)) r (sum_j s_(mu_j) t_(mu_j)) = r`. So
`Phi` is an isomorphism of unital rings and `GL_n(R) ≅ R^x`. The case `n = 1`
is trivial.

**Restriction.** If `A <= R` is a unital subalgebra, `M_n(A) <= M_n(R)` is a
unital subring, so `GL_n(A) <= GL_n(R)`, and `Phi` restricts to an injective
homomorphism `GL_n(A) -> R^x`.

**Payoff.** `R^x` is finitely presented by
`leavitt-unit-group-finitely-presented` and simple by
`binary-leavitt-unit-group-is-simple`. Every subgroup of `GL_n(A)` therefore
embeds in a finitely presented simple group. `∎`
