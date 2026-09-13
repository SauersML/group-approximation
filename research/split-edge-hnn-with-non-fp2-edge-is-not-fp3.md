---
rg: 2
id: split-edge-hnn-with-non-fp2-edge-is-not-fp3
kind: claim
title: "An HNN extension whose non-FP_2 edge group is a retract of the vertex group with FP_2 kernel, on one side, and lies in an FP_2 subgroup on the other side, is not of type FP_3"
distinct_from:
  fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3: that needs every vertex group to have finite rational H_2 and detects infinite rational H_3 with trivial coefficients; this allows vertex groups with bad finiteness and detects the failure with product coefficients through a retraction onto the edge group
  twisted-rope-trick-container-is-not-fp3-over-fp2-hosts: that treats rope-trick containers over hosts with finite rational H_2 or with embeddings agreeing on H_2; this covers containers whose second edge map is a graph over a factor of the vertex group, whatever the rational homology
---

Let `K = HNN(A; L; f_1, f_2)`, with stable letter `t` and relations
`t f_1(y) t^{-1} = f_2(y)` for `y ∈ L`. Suppose:

1. `L` is finitely generated but not of type `FP_2` (over `Z`, or over `Q`);
2. there is a retraction `r: A → L` with `r ∘ f_2 = id_L`, and its kernel `N`
   is nontrivial and of type `FP_2`; equivalently `A = N ⋊ f_2(L)`;
3. `f_1` factors through a subgroup `P ≤ A` of type `FP_2`.

Then `H_2(K; Π_I ZK) ≠ 0` for some index set `I`. So `K` is not of type
`FP_3` (resp. `FP_3(Q)`), and a fortiori not `F_3` or `F_∞`. This holds even
when `K` is finitely presented.

**Mechanism.** On product coefficients, `f_1` contributes nothing in degree 1,
because it passes through `P`, which is `FP_2`. The map induced by `f_2` in
degree 1 is the map on `H_1(L; -)` induced by collapsing the coefficients over
the cosets of `N`. That collapse is a split sum map `⊕_N ZL → ZL`. Its kernel
carries a full copy of the product defect `H_1(L; Π_I ZL) ≠ 0` of the
non-`FP_2` group `L`. That copy survives into `H_2(K; Π_I ZK)` through the
Mayer--Vietoris sequence.

**Application.** It refutes `acyclic-host-twisted-rope-container-is-of-type-fp3`,
see `acyclic-host-twisted-rope-container-is-never-fp3`. More generally: in
Higman's rope trick, sending the double `L` into the host as a graph over a
direct factor `L` leaves the defect of `L` uncancelled in degree 2.
