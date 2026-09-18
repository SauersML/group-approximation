---
rg: 2
id: euler-lamplighter-acts-faithfully-on-the-l-ary-tree
kind: claim
title: The Euler lamplighter G_l acts faithfully on the rooted l-ary tree through l-adic measures on Z_l, with the Euler element acting as multiplication by 1 + l x
distinct_from:
  z-localized-embeds-in-fg-rf-soluble-group: that constructs G_l and proves it residually finite; this gives an explicit faithful action of G_l on the l-ary rooted tree, the setting of the finite-state question.
  euler-lamplighter-has-a-faithful-finite-state-action: that asks whether some faithful action is finite-state; this is one explicit faithful action, and it is not claimed to be finite-state.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
  - research/artifacts/gq-referee-a-euler-lamplighter-acts-faithfully-on-the-l-ary-tree.md
---

**ESTABLISHED (2026-09-18)** through `euler-lamplighter-acts-faithfully-on-the-l-ary-tree-proof`. Lane proof (gq-k2-q),
elementary. *Reviewed:* PASS by `gq-referee-a`
(`research/artifacts/gq-referee-a-euler-lamplighter-acts-faithfully-on-the-l-ary-tree.md`). Nits N1–N4 are applied.

## Setting

As in `z-localized-embeds-in-fg-rf-soluble-group`:
- `M = Z_(l)[y, y^(-1)]` with basis `f_j = y^j`;
- `x` is multiplication by `y^(-1)`;
- `β = 1 + l·y d/dy`, so `β f_j = (1 + lj) f_j`;
- `H = ⟨x, β⟩` and `G_l = M ⋊ H`.

Let `Λ = Z_l[[T]]`.

## Statement

1. **Model.** `ι : M -> Λ`, `y ↦ 1 + T`, is an injective ring map with dense image in the `(l,T)`-adic topology. The
   group `G_l` acts faithfully on `Λ` by continuous affine maps:
   - `m ∈ M` acts by `g ↦ g + ι(m)`;
   - `x` acts by `g ↦ (1+T)^(-1) g`;
   - `β` acts by `β̂ = 1 + lD`, where `D = (1+T) d/dT`.
2. **Measures.** Identifying `Λ` with the Iwasawa algebra of `Z_l`, so that `1 + T` is translation by `1`, `D` is
   multiplication of measures by the coordinate function `x ↦ x`. So `β̂` is multiplication by the unit-valued
   function `1 + l x`.
3. **An l-regular invariant flag.** Let `F_n = (l,T)^n`. Refine `F_n ⊃ F_(n+1)` by
   `E_(n,j) = F_(n+1) + span{l^a T^(n−a) : a >= j}`, for `0 <= j <= n+1`. Each step has index `l`, and the linear
   parts of all elements of `G_l` preserve every `E_(n,j)`.
4. **Tree action.** So `G_l` acts on the rooted `l`-regular tree of cosets of this chain, and faithfully. The boundary
   is `Λ` itself, because `∩ E = 0` and `Λ` is complete. The tree coordinates are the `l`-adic digits `d_(a,b)` of the
   coefficients of `T^b`, read in the order `a + b` ascending, then `a` ascending.

5. **Level images are `l`-groups.** The image of `G_l` in the permutations of each level of the tree is a finite
   `l`-group. So `G_l ≤ Aut(T_l)` is an explicit form of its residual `l`-finiteness. For odd `l` this is not
   automatic from the tree, since the level quotients of `Aut(T_l)` are not `l`-groups.
