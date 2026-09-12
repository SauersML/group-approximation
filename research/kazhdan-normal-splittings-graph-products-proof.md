---
rg: 2
id: kazhdan-normal-splittings-graph-products-proof
kind: route
title: Property (T) fixes a vertex of a minimal Bass--Serre tree, and normality spreads the fixed set to the whole tree
target: kazhdan-normal-subgroups-of-splittings-and-graph-products
requires:
  - graph-product-normal-forms-and-rf-permanence
---

1. **Splittings.** A countable Kazhdan group has Serre's property (FA)
   (Watatani 1982). So `M` fixes a vertex of the Bass--Serre tree `T` of the
   splitting.
   - The fixed-point set `Fix(M)` is a nonempty subtree. It is `H`-invariant,
     because `h Fix(M) = Fix(h M h^-1) = Fix(M)`.
   - The action of `H` on `T` is minimal. In an amalgam with `C` proper in both
     factors the tree has no invariant proper subtree, and the graph of groups
     of an HNN extension has no terminal vertex. So `Fix(M) = T`.
   - Edge stabilizers are the conjugates of `C`. So `M` lies in their
     intersection, which is the normal core of `C` in `H`.
2. **Graph products.** Let `v` be a vertex that is not universal, with link
   `lk(v)` and star `st(v)`.
   - Normal forms give the splitting
     `H = H_(Delta - v) *_(H_lk(v)) H_st(v)`. It is nondegenerate because
     `H_v != 1` and some `w` outside `st(v)` has `H_w != 1`. By step 1,
     `M <= H_lk(v)`.
   - Normal forms also give `H_A cap H_B = H_(A cap B)` for vertex sets `A` and
     `B`. So `M <= H_L`, where `L` is the intersection of the links of the
     non-universal vertices.
   - A vertex `u` of `L` is universal, because `u` does not lie in its own
     link. So `L <= Z` and `M <= H_Z`.
   - The universal vertices span a complete subgraph joined to every other
     vertex. So `H = H_Z x H_(Delta - Z)`.
3. **Consequences.** An amenable Kazhdan group is finite. Direct products of
   sofic groups are sofic. The finite-kernel case of the criterion is recorded
   in `sofic-quotients-by-finite-normal-subgroups-are-sofic`.
