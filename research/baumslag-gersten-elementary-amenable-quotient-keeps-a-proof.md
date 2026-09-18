---
rg: 2
id: baumslag-gersten-elementary-amenable-quotient-keeps-a-proof
kind: route
title: The induced-module tower is a fixed point of the prepend functor, so its complement inclusion is a shift endomorphism, and the ascending HNN extension receives BG
target: baumslag-gersten-elementary-amenable-quotient-keeps-a
requires:
  - bs12-extends-to-amenable-square-conjugation-chain
---

Date: 2026-09-18. Written proof. Notation as in
[[bs12-amenable-square-chain-induced-tower-proof]] (the tower proof):
`Phi(K,c) = V(K,c) rtimes K`, the tower `H_0 = Z`,
`H_(k+1) = Phi(H_k, y^(k)_0)`, the injective maps `iota_k` of its Lemma 3,
and the direct limit `H_inf` with the chain `(y_j)_(j >= 0)`.

**Step 1 (fixed point).** For each `k`, let `theta_k : H_k -> H_(k+1)` be
the inclusion of the complement `H_k <= V(H_k) rtimes H_k = H_(k+1)`. On
chains, `theta_k(y^(k)_j) = y^(k+1)_(j+1)`, by the relabelling in the
definition of the tower. By definition, `iota_(k+1) = Phi(iota_k)`, and
`Phi(iota_k)` restricted to the complement is `iota_k`. So

    iota_(k+1) o theta_k = theta_(k+1) o iota_k.

So the `theta_k` induce a homomorphism `theta : H_inf -> H_inf` with
`theta(y_j) = y_(j+1)`. It is injective, because each `theta_k` is injective
and the `iota_k` are injective.

**Step 2 (ascending HNN).** Let
`A = < H_inf, tau | tau^(-1) h tau = theta(h), h in H_inf >`. By Britton's
lemma for ascending HNN extensions, `H_inf` embeds in `A`, and the normal
closure of `H_inf` is the increasing union
`U_(m >= 0) tau^m H_inf tau^(-m)`. Each term is isomorphic to `H_inf`, and
the quotient is `<tau> = Z`.

`H_inf` is a directed union of solvable groups, so it is elementary
amenable. The class of elementary amenable groups is closed under
increasing unions and under extensions, so `A` is elementary amenable.

**Step 3 (the map).** Define `a -> y_0`, `t -> tau`. Then
`t^(-1) a t -> tau^(-1) y_0 tau = y_1`, and the relator
`(a^t)^(-1) a (a^t) a^(-2)` maps to `y_1^(-1) y_0 y_1 y_0^(-2) = 1`, by the
theorem of the tower proof. So this defines a homomorphism
`BG -> A`. The image `y_0` of `a` has infinite order in `H_inf`, and
`H_inf <= A`.

**Step 4 (configuration).** Put `x_j = tau^(-j) y_0 tau^j` for `j in Z`.
Then `x_j = y_j` for `j >= 0`. Conjugating by powers of `tau`,
`x_(j+1)^(-1) x_j x_(j+1) = x_j^2` holds for all `j in Z`, and
`<x_0,x_1> = <y_0,y_1> = BS(1,2)`. So
`psi : a_j -> x_j` is a homomorphism from the Magnus kernel of `BG` that is
injective on the piece `B_0 = BS(1,2)`. Since `F_-` and `F_+` are subgroups
of `B_0`, `psi` separates all finite sets as (AA) requires. ∎
