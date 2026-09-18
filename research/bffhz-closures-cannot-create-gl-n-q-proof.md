---
rg: 2
id: bffhz-closures-cannot-create-gl-n-q-proof
kind: route
title: Deduce the closure statements from the vertex-fixing property in free splittings
target: bffhz-closures-cannot-create-gl-n-q
requires:
  - gl-n-q-fixes-a-vertex-in-free-splittings
---

Notation as in the target. Items 1 and 2 use
`gl-n-q-fixes-a-vertex-in-free-splittings`, abbreviated (FV). Its hypotheses
hold for `H` and for `H'`: the groups `SL_n(Q)` and `(Q,+)` are in its list.

**Item 1.** `A * B` acts on its Bass--Serre tree with trivial edge
stabilizers, and the vertex stabilizers are the conjugates of `A` and `B`.
Restrict the action to `H` and apply (FV).

**Item 2.**
- **The kernel of the exponent map.** In the ascending HNN extension
  `J *_β = <J, t | t j t^-1 = β(j)>`, the map `t -> 1`, `J -> 0` onto `Z` has
  kernel `L = ⋃_{k >= 0} t^-k J t^k`. That is the standard normal form
  `t^-a j t^b` of an ascending HNN extension.
- **L embeds in `M * F_m`.** Since `β` is an automorphism of `M * F_m`, the map
  `t^-k j t^k -> β^-k(j)` is a well-defined injective homomorphism
  `L -> ⋃_k β^-k(J) <= M * F_m`. It is well defined because
  `t^-k j t^k = t^-(k+1) β(j) t^(k+1)` and `β^-(k+1)(β(j)) = β^-k(j)`. It is
  injective because it is injective on each `t^-k J t^k`.
- **`H'` lies in `L`.** The derived subgroup `H'` maps trivially to the abelian
  group `Z`, and `(Q,+)` does too, being divisible. So `H' <= L`.
- **Conclusion.** `M * F_m` is the fundamental group of the graph of groups
  with one vertex group `M` and `m` loops with trivial edge groups. Its
  Bass--Serre tree has trivial edge stabilizers, and its vertex stabilizers are
  the conjugates of `M`. By (FV), `H'` lies in a conjugate of `M`.

**Item 3.**
- **The map to `Aut(F_m)`.** An automorphism fixing `M` pointwise preserves
  `N = <<M>>`, so it induces an automorphism of `(M * F_m)/N ≅ F_m`. This gives
  a homomorphism `Aut_M(M * F_m) -> Aut(F_m)`.
- **Divisible elements die.** `Aut(F_m)` is residually finite (Baumslag,
  J. London Math. Soc. 38 (1963), 117–118: automorphism groups of finitely
  generated residually finite groups are residually finite). A residually
  finite group contains no nontrivial divisible element: in each finite
  quotient the image of a divisible subgroup is a divisible finite group, hence
  trivial. So every divisible element of `Aut_M(M * F_m)` maps to `1`.
- **Hence `SL_n(Q) <= K_M` for `GL_n(Q)` or `SL_n(Q)`.** Each root element
  `1 + q e_ij` is divisible, since it is `(1 + (q/k) e_ij)^k`. The kernel `K_M`
  is normal, so it contains the normal closure of the root subgroups, which is
  `SL_n(Q)`. For `U_3(Q)` every element is divisible, and `(Q,+)` is divisible.
- **Restriction to `N` is injective on `K_M`.** For `α ∈ K_M`, `α(x_i) = x_i k_i`
  with `k_i ∈ N`, because `α` induces the identity modulo `N`. Suppose
  `α|_N = id`. For `n ∈ N` we have `x_i n x_i^-1 ∈ N`, so
  `x_i n x_i^-1 = α(x_i n x_i^-1) = x_i k_i n k_i^-1 x_i^-1`. Thus `k_i` is in
  the centre of `N`. By Kurosh, `N` is the free product of the conjugates
  `w M w^-1`, `w ∈ F_m`. Since `m >= 1` and `M != 1` there are at least two
  factors, so `N` has trivial centre. Hence `k_i = 1` and `α = id`.
- **The restriction conjugates each factor.** For `g ∈ M` and `w ∈ F_m`, write
  `α(w) = w n` with `n ∈ N`. Then
  `α(w g w^-1) = (w n w^-1) (w g w^-1) (w n w^-1)^-1`, and `w n w^-1 ∈ N`.
- **Right translations.** The maps `x_i -> x_i g` (`g ∈ M`, other letters
  fixed) lie in `K_M` and satisfy `α_g ∘ α_h = α_(gh)`, so they give a copy of `M` for each letter. Maps
  for different letters commute, so together they give `M^m`.

**The `M = V` remark.** `V` contains no `(Q,+)` (Higman; BBMZ survey
arXiv:2306.16356v3, Theorem 4.4), and `(Q,+)` lies in each `H'`. Items 1 and 2
then exclude every group in the list.
