---
rg: 2
id: separating-sofic-quotient-sets-make-an-action-sofic-proof
kind: route
title: Pull labels back along separating equivariant maps, take product models, and intersect amenable Mikhailova quotients
target: separating-sofic-quotient-sets-make-an-action-sofic
requires:
  - gkp-sofic-action-toolkit
  - gkp-amenable-group-actions-are-sofic
  - gkp-free-generalized-wreath-soficity
  - centralizer-hnn-is-free-generalized-wreath
---

Definition 2.1(3) of GKP, as quoted in `co-amenable-induction-of-sofic-actions-proof`:
an orbit approximation consists of a good set `S` and injective labels
`pi_s : E -> B` with `pi_(phi(g)s)(x) = pi_s(g^-1 x)` whenever `s in S`,
`g in F`, `x in E`, `phi(g)s in S` and `g^-1 x in E`.

## (S1)

Given finite `F`, `E` and `epsilon`, choose `β : G ↷ Y` and `p` injective on
`E`. Take `psi : G -> Sym(A)` unital, `(F, epsilon)`-multiplicative, and an
`(F, p(E), epsilon)`-orbit approximation of `β`, with good set `S` and labels
`pi^Y_s`. For `s in S` and `x in E` put `pi_s(x) = pi^Y_s(p(x))`. This label is
injective because `p` is injective on `E`. Let `s in S`, `g in F`, `x in E`
with `psi(g)s in S` and `g^-1 x in E`. Then `p(x) in p(E)` and
`β(g^-1)p(x) = p(g^-1 x) in p(E)`, so

```text
pi_(psi(g)s)(x) = pi^Y_(psi(g)s)(p(x)) = pi^Y_s(p(g^-1 x)) = pi_s(g^-1 x).
```

So `psi` is an `(F, E, epsilon)`-orbit approximation of `α`.

## (S2)

Given finite `F <= G_1 x G_2`, `E <= X_1 x X_2` and `epsilon`, let `F_i` and
`E_i` be the coordinate projections. Choose `epsilon'` with
`(1-epsilon')^2 > 1-epsilon`. Take models `phi_i : G_i -> Sym(A_i)` that are
unital, `(F_i, epsilon')`-multiplicative, and `(F_i, E_i, epsilon')`-orbit
approximations, with good sets `S_i` and labels `pi^i`. Put `A = A_1 x A_2`,
`phi(g_1,g_2) = phi_1(g_1) x phi_2(g_2)`, `S = S_1 x S_2`, and
`pi_s(x_1,x_2) = (pi^1_(s_1)(x_1), pi^2_(s_2)(x_2))`.

`phi(gh)` and `phi(g)phi(h)` agree on the product of the two coordinate
agreement sets, a proportion above `(1-epsilon')^2`. The product labels are
injective. If `phi(g)s in S` and `g^-1 x in E`, the same holds in each
coordinate, and equivariance holds coordinatewise. This is the computation in
the proof of GKP Proposition 2.16, with the groups multiplied as well as the
sets.

## (C1) and (C2)

Let `E <= G/K` be finite. For each pair `aK != bK` in `E`, `a^-1 b notin K`,
so some `K_i` of the given family avoids `a^-1 b`. Let `K'` be the
intersection of these finitely many `K_i`. Then `G/K -> G/K'` is equivariant
and injective on `E`.

- In (C1), `K'` has finite index, and `G ↷ G/K'` is sofic by GKP Remark 2.18.
- In (C2), `core(K') = ∩ core(K_i)`, and `G/core(K')` embeds in
  `∏ G/core(K_i)`, which is amenable. The action `G ↷ G/K'` factors through
  `G/core(K')`, so it is sofic by GKP Theorem 2.17
  ([[gkp-amenable-group-actions-are-sofic]]) and Proposition 2.15(1)
  ([[gkp-sofic-action-toolkit]]).

In both cases apply (S1).

## (C3)

Write `N = ker φ`. Residual amenability of `Q` says that `N` is the
intersection of normal subgroups `N_i` of `F` with each `F/N_i` amenable. Put

```text
M_i = { (u,v) : u v^-1 in N_i }  >=  M_Q.
```

Since `u =_Q v` iff `u v^-1 in N`, we have `∩_i M_i = M_Q`. Also
`N_i x N_i` is normal in `F x F` and contained in `M_i`, so
`(F x F)/core(M_i)` is a quotient of `(F/N_i) x (F/N_i)`, which is amenable.
By (C2), `F x F ↷ (F x F)/M_Q` is sofic. `F x F` is residually finite, hence
sofic. GKP Theorem 3.7 ([[gkp-free-generalized-wreath-soficity]]) makes
`L wr^*_((F x F)/M_Q) (F x F)` sofic for every sofic `L`. With `L = Z`, this
is the rope `< F x F, v | [v, M_Q] = 1 >` by
[[centralizer-hnn-is-free-generalized-wreath]]. `∎`

(S2) is not used in (C1)--(C3). It is recorded for product actors such as
`K_e = K_e^0 x K^g` in the compiler rope.
