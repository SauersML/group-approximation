---
rg: 2
id: free-kernel-tree-actions-embed-in-free-generalized-wreath
kind: claim
title: A group acting on a tree with a normal subgroup acting freely embeds in the free generalized wreath product of Z over the quotient's action on oriented edges
distinct_from:
  gkp-free-generalized-wreath-soficity: that imports the soficity of free generalized wreath products over sofic actions; this supplies the embedding that feeds groups acting on trees into it
  centralizer-hnn-is-free-generalized-wreath: that identifies one centralizer HNN extension as a free generalized wreath product; this embeds every free-kernel tree action, through edge paths projected to the quotient graph
  radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups: that embeds the metabelian quotient of Radu's lattice in chains modulo square boundaries; this projects to the vertical tree, where no boundaries have to be divided out
---

**ESTABLISHED (unreviewed).** Let a group `Γ` act on a tree `T`, and let `Λ ◁ Γ` act freely, fixing
no vertex and inverting no edge. Put `Q = Γ/Λ` and `Y = Λ\T` with its induced `Q`-action, and let
`E^±(Y)` be the `Q`-set of oriented edges of `Y`. Then:

1. **Free lamps.** There is an injective homomorphism

   ```text
   Γ  ↪  Z ≀^*_(E^±(Y)) Q  =  ( *_(e ∈ E^±(Y)) Z_e ) ⋊ Q.
   ```

2. **Abelian lamps.** It induces an injective homomorphism

   ```text
   Γ/[Λ,Λ]  ↪  Z ≀_(E^±(Y)) Q  =  ( ⊕_(e ∈ E^±(Y)) Z ) ⋊ Q.
   ```

3. **Soficity.** Suppose `Q` is sofic and, for one oriented edge `e` in each `Q`-orbit of `E^±(Y)`,
   the coset action `Q ↷ Q/Stab_Q(e)` is sofic (GKP Definition 2.1(5)). Then `Γ` and `Γ/[Λ,Λ]` are
   sofic. Here `Stab_Q(e)` is the image of the oriented-edge stabilizer `Stab_Γ(ẽ)` of a lift, which
   `Λ` meets trivially.

Both embeddings send `g` to `(d(g), gΛ)`, where `d(g)` records the projection to `Y` of the geodesic
from a base vertex to its `g`-translate. This is the tree form of the Magnus embedding. Its point is
that it has no quotient: soficity of a free-kernel cover reduces to a set action of the quotient.

Proof in `free-kernel-tree-actions-embed-in-free-generalized-wreath-proof`.
