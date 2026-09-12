---
rg: 2
id: finite-index-edge-hnn-embeds-in-fp-simple-group
kind: claim
title: An HNN extension of a finitely presented group over finite-index subgroups that acts faithfully on its Bass-Serre tree embeds in a finitely presented simple group
distinct_from:
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence for finitely generated, possibly infinite-index edges over a group already inside a finitely presented simple group; this is the finite-index case with a faithful tree action, which needs no envelope for the vertex group, and it records where that method stops.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that is the general literature theorem for cocompact actions on locally finite trees; this specializes it to one-vertex graphs of groups, states the faithfulness hypothesis on the HNN extension itself, and derives the limits that matter for the Boone--Higman tower route.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports two families from the same paper; this is a theorem for arbitrary finitely presented vertex groups, whose case A = Z contains BS(m,n) with |m| != |n|.
---

**ESTABLISHED.** Let `A` be a finitely presented group, let `C_1, C_2 <= A` be
subgroups of finite index, let `phi : C_1 -> C_2` be an isomorphism, and let

```text
K = A*_phi = < A, t | t c t^-1 = phi(c), c in C_1 >.
```

If no nontrivial normal subgroup of `K` is contained in `A`, then `K` embeds in
a finitely presented simple group.

The hypothesis says exactly that `K` acts faithfully on its Bass--Serre tree,
whose kernel is the intersection of the conjugates of `A`. No envelope for `A`
and no decidability hypothesis is assumed; both are consequences. By (L1) `A` is
residually finite, so it has solvable word problem, and a finite-index subgroup
of a finitely presented group has decidable membership (Todd--Coxeter).

## Where the method stops

(L1) **Residually finite vertex group.** Faithfulness forces `A` to be
residually finite. The theorem never applies when `A` has a nontrivial finite
residual.

(L2) **Finitely presented simple vertex groups give only mapping tori.** An
infinite simple group has no proper subgroup of finite index. So for `A` an
infinite finitely presented simple group the hypotheses force `C_1 = C_2 = A`
and `K = A ⋊_phi Z`. Its Bass--Serre tree is a line, and `A` lies in the
kernel, so the theorem says nothing. Attempt 2 of
`bh-embeddability-survives-decidable-edge-hnn` leads to HNN extensions of
finitely presented simple groups, and the finite-index case among those is
exactly this one.

(L3) **Infinite-index edges cannot be converted.** The HNN subgroup theorem
puts `A*_phi` inside `B*_psi` when `A <= B`, `D_1, D_2 <= B`, `A ∩ D_i = C_i` and
`psi` extends `phi`. Then `[A : C_i] <= [B : D_i]`. So an HNN extension with an
infinite-index edge cannot be embedded stable letter to stable letter into one
with finite-index edges, and its tree stays locally infinite.

(L4) **The non-faithful repair needs residual finiteness again.** The
enlargement in Theorem 11.1 of
`bliw-locally-finite-tree-actions-embed-in-fp-simple-groups` needs a faithful
graph of groups whose vertex groups are commensurable with `A`. Those vertex
groups are residually finite by the argument of (L1), and residual finiteness is
a commensurability invariant. This is the boundary the authors state.

The derivation is `finite-index-edge-hnn-embeds-in-fp-simple-group-proof`.
