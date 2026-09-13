---
rg: 2
id: measure-full-group-subgroups-hyperlinear-if-crossed-product-ce
kind: claim
title: If a Cantor action has an essentially free invariant measure of full support and a Connes-embeddable crossed product, every subgroup of its topological full group is hyperlinear
distinct_from:
  full-group-subgroup-trace-generation-dichotomy: that computes the canonical trace of full-group unitaries in a relation factor and shows subgroups cannot regenerate a non-CE relation factor; this is the positive transfer of Connes embeddability from the crossed product to the topological full group.
  amenable-orbit-full-group-subgroups-are-sofic: that gives soficity when the acting group is amenable; this needs no amenability, only Connes embeddability of the crossed product, and concludes hyperlinearity.
  lrf-cantor-actions-give-lef-full-and-elementary-groups: that builds combinatorial finite models from local residual finiteness; this uses a tracial embedding of the measure crossed product and needs no finite models of the action.
---

**ESTABLISHED** by route `measure-full-group-hyperlinear-via-crossed-product-proof`. Not independently reviewed. No
novelty is claimed: the representation of full-group elements as unitaries of the crossed product is standard, and
the conclusion is a corollary of the hyperlinearity dictionary.

**Setting.**
- `G` is a countable group acting continuously on a Cantor space `X` by `alpha`.
- `mu` is a `G`-invariant Borel probability measure on `X` with full support, and the action is essentially free for
  `mu`: `mu(Fix(g)) = 0` for every `g != e`.
- `M = L^infinity(X, mu) ⋊ G` is the crossed-product von Neumann algebra with its canonical trace `tau = mu ∘ E`.
- `[[alpha]]` is the topological full group: homeomorphisms `gamma` of `X` with a finite clopen partition
  `X = U_1 ⊔ ... ⊔ U_k` and `g_1, ..., g_k` in `G` such that `gamma = alpha(g_j)` on `U_j`.

**Theorem.**
1. The map `gamma ↦ u_gamma = Σ_j lambda_(g_j) 1_(U_j)` is a well-defined injective group homomorphism
   `[[alpha]] -> U(M)`, with `tau(u_gamma) = mu({x : the piece of gamma containing x has g_j = e})`.
2. If `M` is Connes-embeddable, then every subgroup of `[[alpha]]` is hyperlinear.

**Contrapositive fence.** If some subgroup of `[[alpha]]` is non-hyperlinear and `alpha` carries an essentially free
invariant probability measure of full support, then `L^infinity(X, mu) ⋊ G` is not Connes-embeddable. So a
non-hyperlinear witness inside a topological full group needs either an action with no such measure, or a
non-Connes-embeddable measure crossed product.

**Instances.**
- `G` amenable: `M` is hyperfinite, so the conclusion holds. Main's `amenable-orbit-full-group-subgroups-are-sofic`
  already gives the stronger soficity there.
- `G = F_r` with an invariant measure of full support: Ma's Theorem C gives the stronger LEF conclusion (see
  `free-group-crossed-product-matricial-iff-invariant-measure`).
