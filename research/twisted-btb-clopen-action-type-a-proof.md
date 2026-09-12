---
rg: 2
id: twisted-btb-clopen-action-type-a-proof
kind: route
title: Refine brick partitions, match Boolean atoms brick by brick, and split stabilizers along the clopen partition
target: twisted-btb-clopen-action-is-type-a
requires:
  - twisted-brin-thompson-finite-presentation-criterion
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

Notation as in the target. For finitely supported `u, w` write `u⋆w` for
coordinatewise concatenation, so that `h_u h_w = h_(u⋆w)`. Two identities are
used throughout:

```text
τ_g h_w = h_(w∘g^-1) τ_g,        h_(u⋆w)^-1 = h_w^-1 h_u^-1 .
```

**(1) Finite presentation.** The action of `G` on `S` is faithful and of type
(A), so `SV_G` is finitely presented by
`twisted-brin-thompson-finite-presentation-criterion` (Zaremsky,
arXiv:2405.18354, Theorem A).

**(2) Clopen sets are brick unions.** Bricks form a basis of the product
topology, and two bricks meet in a brick or not at all. A nonempty clopen
`X ⊆ C^S` is compact, hence a finite union of bricks. All of them depend on a
finite set `T` of coordinates and on prefixes of length at most `d`. The bricks
`B(u)` with `supp u = T` and `|u(s)| = d` partition `C^S`, and each lies in `X`
or in its complement. So `X` is a finite disjoint union of bricks. Splitting one
brick `B(u)` along a coordinate `s` into `B(u[s -> u(s)0])` and
`B(u[s -> u(s)1])` raises the count by one. Hence `X` is a disjoint union of `m`
bricks for every `m` at least its minimal count.

**(3) Restriction of a branch.** A brick inside `B(u)` has the form `B(u⋆w)`.
On it the branch `h_v τ_g h_u^-1` equals `h_(v⋆(w∘g^-1)) τ_g h_(u⋆w)^-1`, again a
branch. So any finite brick refinement of the source partition of `f` gives
another branch description of `f`.

**(4) Transitivity on partitions.** If `{B(u_i)}` and `{B(v_i)}` are brick
partitions of `C^S` with the same number of pieces, the map equal to
`h_(v_i) h_(u_i)^-1` on `B(u_i)` lies in `SV_G`, with `g_i = 1`, and sends
`B(u_i)` onto `B(v_i)`.

**(5) Orbits on tuples.** Take `(U_1,...,U_k)` and `(U'_1,...,U'_k)` in `Ω^k`.
For `ε in {0,1}^k` let `A_ε` be the intersection of the `U_i` with `ε_i = 1` and
the complements of the others, and define `A'_ε` in the same way. Suppose
`A_ε = ∅` exactly when `A'_ε = ∅`. By (2), choose for each nonempty atom a common
brick count for `A_ε` and `A'_ε`. The resulting brick partitions of `C^S` have
equal size, and (4) gives `f in SV_G` with `f(A_ε) = A'_ε` for all `ε`, hence
`f(U_i) = U'_i`. Conversely every homeomorphism preserves the atom pattern.

There are finitely many patterns. For ordered pairs they are the `2 x 2`
0/1-matrices with no zero row or column: seven of them. Forgetting order merges
the two containment patterns, and removing equality leaves five orbits of
two-element subsets.

**(6) Faithfulness.** If `f(κ) != κ`, choose a proper brick `B` containing `κ`
and not `f(κ)`. Then `f(B) != B`.

**(7) Stabilizers split.** Let `f(U) = U`. By (2) and (3), refine a branch
description of `f` so that every source brick lies in `U` or in `U^c`. Since
`f(U) = U`, the branches from bricks in `U` have images partitioning `U`, and
likewise for `U^c`. Let `f_U` use the branches of `f` on `U` and identity
branches on a brick partition of `U^c`. Then `f_U in D(U)`, and similarly
`f_(U^c) in D(U^c)`. These commute, meet trivially, and multiply to `f`. So
`Stab(U) = D(U) x D(U^c)`.

**(8) Supported copies.** Let `B(p)` be a proper brick and `f in SV_G`. By the
identities above, `h_p f h_p^-1` equals `h_(p⋆v_i) τ_(g_i) h_(p⋆u_i)^-1` on
`B(p⋆u_i)`. These bricks partition `B(p)`. Extended by identity branches on
`C^S \ B(p)`, it lies in `D(B(p))`.

Conversely, let `k in D(B(p))`. Refine its description as in (7). Branches on
bricks in `B(p)` have the form `h_(p⋆v) τ_g h_(p⋆u)^-1`. Discard the branches
outside `B(p)`, where `k` is the identity, and conjugate back to
`h_v τ_g h_u^-1`. The sources `B(u)` partition `C^S`, so `h_p^-1 k h_p in SV_G`.

The two conjugations are inverse homomorphisms, so `D(B(p)) ≅ SV_G`. Every
`U in Ω` is moved onto a proper brick by (5). Hence `D(U) ≅ SV_G`, and
`D(U^c) ≅ SV_G` for the same reason.

Together, (1), (6), (5) and (7)--(8) give the four clauses of type (A). `∎`
