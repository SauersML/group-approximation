---
rg: 2
id: gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups-proof
kind: route
title: Exhaust GL_n(Q) by finitely generated subgroups, embed each by Zaremsky's theorem, and pass to an ultraproduct
target: gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups
requires: [rational-linear-groups-satisfy-boone-higman]
---

**Clause 1.**
- **Exhaustion.** Enumerate `GL_n(Q) = {g_1, g_2, …}` and let `H_i = <g_1, …, g_i>`.
  Each `H_i` is finitely generated, `H_i <= H_(i+1)`, and `⋃ H_i = GL_n(Q)`.
- **One host each.** By `rational-linear-groups-satisfy-boone-higman` (Zaremsky,
  arXiv:2405.09722, Theorem 1.2), each `H_i` has an embedding `ι_i : H_i -> K_i`
  in a finitely presented simple group `K_i`.
- **The map.** For `g in GL_n(Q)` let `x_i(g) = ι_i(g)` if `g in H_i` and
  `x_i(g) = 1` otherwise. Define `Φ(g)` as the class of `(x_i(g))_i` in `∏_U K_i`.
- **Homomorphism.** Given `g, h`, both lie in `H_i` for all `i` beyond some
  `i_0`, and then `x_i(gh) = x_i(g) x_i(h)`. The set of such `i` is cofinite, so
  it lies in the nonprincipal `U`. So `Φ(gh) = Φ(g) Φ(h)`.
- **Injective.** If `g ≠ 1`, then `x_i(g) = ι_i(g) ≠ 1` for all `i >= i_0`, so
  `Φ(g) ≠ 1`.

**Clause 2.** Let the system have a solution `y = (a_1, …, a_r)` in `GL_n(Q)`.
All `a_j` lie in some `H_i`. The equations and inequations are quantifier-free,
so the injective homomorphism `ι_i` carries the solution to one in `K_i`.

**Clause 3.** Let `∀y θ(y)` hold in every finitely presented simple group, with
`θ` quantifier-free, and let `a` be a tuple in `GL_n(Q)`. As in clause 2,
`a ⊂ H_i` for some `i`, and `θ(ι_i(a))` holds in `K_i`. Injective homomorphisms
preserve and reflect quantifier-free formulas, so `θ(a)` holds in `H_i`, hence
in `GL_n(Q)`. ∎

Clauses 2 and 3 use only the embeddings `ι_i`, not the ultraproduct. By Łoś's
theorem, clause 1 is an equivalent packaging.
