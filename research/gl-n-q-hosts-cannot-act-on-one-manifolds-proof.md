---
rg: 2
id: gl-n-q-hosts-cannot-act-on-one-manifolds-proof
kind: route
title: Witte's circle theorem plus compactification of the line excludes finite-index subgroups of SL(3,Z) from homeomorphism groups of one-manifolds
target: gl-n-q-hosts-cannot-act-on-one-manifolds
requires:
  - sl-n-z-circle-actions-factor-through-finite-groups
---

**Step 0: each component reduces to the circle.** Let `C` be a connected
one-manifold. If `C` is not a circle, it is homeomorphic to `R`, `[0,1)` or
`[0,1]`. Homeomorphisms preserve the boundary, so they preserve the interior
`int C`, which is homeomorphic to `R`. A homeomorphism of `C` is determined by
its restriction to the dense subset `int C`, so restriction
`Homeo(C) -> Homeo(int C)` is injective. Every homeomorphism of `R` extends
uniquely to a homeomorphism of the one-point compactification `R ∪ {∞} = S^1`
fixing `∞`. So `Homeo(C)` embeds in `Homeo(S^1)` for every connected
one-manifold `C`.

**Step 1: part 1.** Suppose `Γ <= H <= Homeo(M)`, where `M` has components
`C_1, ..., C_k` and `Γ` is isomorphic to a finite-index subgroup of `SL(3,Z)`.
`H` permutes the components. So the kernel `Γ_0` of `Γ -> Sym(k)` has finite
index in `Γ`, preserves each `C_i`, and is again isomorphic to a finite-index
subgroup of `SL(3,Z)`. By Step 0, each restriction `Γ_0 -> Homeo(C_i)` gives an
action of `Γ_0` on the circle. By `sl-n-z-circle-actions-factor-through-finite-groups`
(with `n = 3`), it has finite image, i.e. a kernel `K_i` of finite index in `Γ_0`.
The action on `M` is faithful, so `K_1 ∩ ... ∩ K_k = 1`. This intersection has
finite index in `Γ_0`, so `Γ_0` is finite. But `Γ_0` has finite index in the
infinite group `SL(3,Z)`. Contradiction.

For `n >= 3`, `A -> diag(A, I_{n-3})` embeds `SL(3,Z)` in `SL_n(Z)`, `GL_n(Z)`,
`SL_n(Q)` and `GL_n(Q)`. So none of these groups embeds in `H`, whatever the
embedding.

**Step 2: part 2.** Let `M` be connected and not a circle. By Step 0 it suffices
to treat `g in Homeo(R)` of finite order `k`. If `g` is increasing and
`g(x) > x` for some `x`, then `g^j(x) > x` for all `j >= 1` by induction
(`g^(j+1)(x) = g(g^j(x)) > g(x) > x`), contradicting `g^k = id`. The case
`g(x) < x` is symmetric. So an increasing finite-order `g` is the identity. If
`g` is decreasing, `g^2` is increasing of finite order, so `g^2 = id`. Hence
every finite-order element has order at most 2, and no element of order 3 acts
faithfully.

The matrix `A = [[0,-1],[1,-1]] in SL_2(Z)` has order 3:
`A^2 = [[-1,1],[-1,0]]` and `A^3 = I`. It lies in `SL_2(Q)` and, by
`A -> diag(A, I_{n-2})`, in `GL_n(Q)` for every `n >= 2`.
