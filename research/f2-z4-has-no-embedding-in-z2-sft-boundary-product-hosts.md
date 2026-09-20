---
rg: 2
id: f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts
kind: claim
title: For every Z^2-Cantor system Ω, every d and every field k, k[Z^4] has no injective algebra map into any matrix ring over B_Ω ⊗ L_∂; so the Z^4 test case and the Z^2-SFT boundary-product host claim are false
distinct_from:
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that is the positive statement, and this is its negation, strengthened to every field, every Z^2-Cantor system, matrix amplification and non-unital maps. This claim refutes it.
  decidable-algebras-embed-in-z2-sft-boundary-product-hosts: that is (E). Z^4 is decidable, so this claim refutes (E).
  z4-has-no-monomial-embedding-in-boundary-product-hosts: that excludes only monomial embeddings. This excludes all algebra embeddings.
  finite-field-polynomial-growth-hosts-bound-commuting-rank: that excludes gauge-homogeneous embeddings over finite fields. This excludes all embeddings over all fields.
---

**ESTABLISHED** by `z4-host-refutation-from-crossed-product-commuting-rank` (unreviewed).

Let `k` be a field and `d >= 1`. Let `Ω` be any compact totally disconnected space with a `Z^2`-action by
homeomorphisms; every free minimal `Z^2`-SFT is one. Put
- `B_Ω = LC(Ω, k) ⋊ Z^2`;
- `L_∂ = LC(∂F_d, k) ⋊ F_d`.

Then for every `r >= 1`, no algebra map `k[x_1^(±1), ..., x_4^(±1)] -> M_r(B_Ω ⊗ L_∂)` is injective, unital or
not. More generally, `M_r(B_Ω ⊗ L_∂)` has no four commuting algebraically independent elements.

**Consequences for the BH chain.**
- `f2-z4-embeds-in-z2-sft-boundary-product-hosts` is false. Take `k = F_2`: no Ω, no `d`, and no corner embedding
  exists.
- `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` (E) is false, because `F_2[Z^4]` is a decidable group
  algebra. So the route `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts` cannot close as stated.
- More sharply, a group algebra `F_2[G]` embeds in no such host once `G` contains `Z^4`. More generally still, it
  embeds in no host `LC(X) ⋊ P` once `G ⊇ Z^(n)` with `n > cd_(F_2) P`
  (`cantor-crossed-products-bound-commuting-rank-by-cd`).
- Not refuted: `decidable-group-algebras-have-fp-cantor-crossed-hosts`, where the acting group `P` may depend
  on `G`. Any host for `F_2[G]` must now have `cd_(F_2) P` at least the commuting rank of `F_2[G]`, which is at
  least the largest rank of a free abelian subgroup of `G`.
