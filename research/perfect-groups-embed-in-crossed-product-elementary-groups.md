---
rg: 2
id: perfect-groups-embed-in-crossed-product-elementary-groups
kind: claim
title: The derived subgroup of the acting group embeds in the elementary group of the crossed product, and K_1 is the only obstruction
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that is the residually finite assembly, with a Toeplitz subshift and an Ore overgroup; this is the embedding lemma for an arbitrary acting group, with the exact obstruction for the elements outside the derived subgroup.
  shift-unit-of-subshift-crossed-product-is-not-elementary: that is the case `Δ = Z`, where the obstruction is nonzero; this states the general criterion of which that is an instance.
artifacts:
  - research/artifacts/sk-sofic-embedding-a-rank-route-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Δ` be a group acting on a compact totally disconnected space `X`, let `k` be a field,
`R = LC(X,k) ⋊ Δ`, and `u: Δ → R^×` the canonical units. Then:

1. `γ ↦ diag(u_γ, 1, 1)` is an injective homomorphism `Δ → GL_3(R)`.
2. `γ ↦ [u_γ]` is a homomorphism `Δ → K_1(R)`, and `diag(u_γ,1,1)` lies in the elementary subgroup `E(R)` if and only
   if `[u_γ] = 0`. So the set of such `γ` is a normal subgroup of `Δ`.
3. `[Δ,Δ]` lies in that subgroup, and already in `EL_3(R)`: if `γ = [α,β]` then

       diag(u_γ,1,1) = diag(u_α,u_α^(-1),1)·diag(u_β,u_β^(-1),1)·diag((u_β u_α)^(-1), u_β u_α, 1) ,

   and each factor is elementary by Whitehead's lemma.

In particular, if `Δ` is perfect then `Δ` embeds in `EL_3(R)`.

**Sharpness.** For `Δ = Z` and an infinite minimal subshift, `K_1(R) = Z` carries `[u]` to a generator
(`binary-subshift-ring-k1-is-half-orbit-index`), and `diag(u,1,1)` is not elementary
(`shift-unit-of-subshift-crossed-product-is-not-elementary`), matching `[Z,Z] = 1`.

Route: `perfect-groups-embed-in-crossed-product-elementary-groups-proof`.

**Review (sk-verify-4, 2026-09-13): PASS.** Injectivity of `u`, the `K_1` class criterion for the stable `E(R)`, and the three-factor Whitehead identity landing `[Δ,Δ]` in `EL_3(R)` re-derived. The title's "only obstruction" concerns the stable elementary group. See `research/artifacts/sk-review-4-2026-09-13-part5.md` §1.
