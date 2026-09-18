---
rg: 2
id: twisted-lamplighter-point-character-gives-extensive-amenability
kind: claim
title: An invariant mean for a cocycle-twisted lamplighter action whose point characters are nontrivial forces extensive amenability
distinct_from:
  affine-lamplighter-amenable-iff-extensively-amenable: that is the untwisted affine action of the lamplighter group on its lamps (Juschenko–Monod Lemma 3.1); this is the twisted action of G alone through a 1-cocycle, which is a smaller group acting, and needs nontrivial point characters.
  jones-subgroup-cosets-form-a-parity-lamplighter: that identifies one twisted lamplighter model of F/\vec F; this is a general principle about any twisted lamplighter.
---

**ESTABLISHED.** Let a group `G` act on a set `X`, let `A` be an abelian group, and let `A^(X)` be the finitely
supported functions `X → A`, with `(g·f)(x) = f(g⁻¹x)`. Let `c: G → A^(X)` be a 1-cocycle,
`c(gh) = c(g) + g·c(h)`, and let `G` act on `A^(X)` by `g⋆f = g·f + c(g)`.

For `x ∈ X` the **point character** is `ψ_x: G_x → A`, `ψ_x(g) = c(g)(x)`. It is a homomorphism on the
stabilizer `G_x`, and `ψ_(kx)(kgk⁻¹) = ψ_x(g)`, so its triviality depends only on the orbit of `x`.

**Statement.** Suppose `ψ_x ≠ 0` for every `x ∈ X`. If the action `⋆` of `G` on `A^(X)` admits a
`G`-invariant mean, then `G ↷ X` is extensively amenable.

**What it kills.** Twisting a lamplighter action by a cocycle does not give a weaker, more accessible
certificate. As soon as every point character is nontrivial, amenability of the twisted affine action of
`G` alone is at least as strong as extensive amenability of the base. The only twisted models not covered
are those where some orbit has trivial point character.

Proof route: `twisted-lamplighter-point-character-difference-mean-proof`.
