---
rg: 2
id: signed-thompson-algebra-is-odd-measure-crossed-product
kind: claim
title: The signed Thompson units span a crossed product over odd two-valued measures that already maps onto the ternary Leavitt algebra
distinct_from:
  leavitt-unit-group-algebra-surjects-onto-leavitt: that is the additive-span surjection of the whole unit group algebra; this identifies the group algebra of one explicit subgroup, the signed Thompson group, with an algebraic crossed product over the space of odd F_2-valued finitely additive measures, and shows that it alone surjects.
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

Let `R = L_(F_3)(1,2)`, `G = R^x` and `X = {0,1}^N`.
* `E = {tau_C = 1 - 2 P_C : C clopen}` is a subgroup of `G` isomorphic to `C(X, F_2)`, with
  `tau_C tau_D = tau_(C triangle D)` and `tau_X = z = -1`.
* Thompson's group `V` (units `sum S[alpha_i] T[beta_i]`) normalizes `E` by `g tau_C g^-1 = tau_(gC)`,
  and `E cap V = 1`.
* So `H = E ⋊ V` is the group of signed permutation units.

Let `M_-` be the space of finitely additive measures `mu` on the clopens of `X` with values in `F_2`
and `mu(X) = 1`. `V` acts on it by pushforward.

1. `F_3[H] eps_- ~= C(M_-, F_3) ⋊_alg V`, with `[tau_C]` going to `mu -> (-1)^(mu(C))` and
   `q_C = eps_- 2(1 - [tau_C])` going to the indicator of `{mu(C) = 1}`.
2. The evaluation `pi : F_3[G] -> R`, restricted to this subalgebra, is evaluation of functions at
   Dirac measures followed by the germ quotient. Its image is all of `R`.
3. An idempotent `1_U` lies in `ker pi` iff the clopen `U` contains no Dirac measure. This accounts
   for the kernel idempotent `eps_-(1 + [h1] + [h2] + [h1 h2])` of `gk-l3-kernel`.

Theorem 2 of the artifact.
