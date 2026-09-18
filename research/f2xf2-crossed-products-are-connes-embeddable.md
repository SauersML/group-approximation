---
rg: 2
id: f2xf2-crossed-products-are-connes-embeddable
kind: claim
title: Every p.m.p. action of F2 x F2 has a Connes-embeddable crossed product
distinct_from:
  f2xf2-in-paunescu-class: that asks for soficity of every action; soficity of an action implies Connes embeddability of its crossed product, so that claim implies this one, and no converse is known.
  tree-lattices-hyperlinear-if-f2xf2-crossed-products-ce: that is one consequence of this hypothesis, for lattices in products of trees.
  sl2-pair-witnesses-need-non-ce-f2xf2-action: that is the implication from this hypothesis (in its F2^(|S|+1) form) to hyperlinearity of all pair-transfer groups over SL2(Z[1/S]).
---

**OPEN.** For every p.m.p. action `F_2 × F_2 ↷ (X, μ)` on a standard probability space, the
crossed product `L^∞(X, μ) ⋊ (F_2 × F_2)` embeds trace-preservingly into `R^ω`.

In the notation `𝒜` of `sl2-pair-witnesses-need-non-ce-f2xf2-action`, this says
`F_2 × F_2 ∈ 𝒜`. The stronger form for all `k` is `F_2^k ∈ 𝒜`.

**Stakes both ways.**
- **If true, including the `F_2^k` forms.** Every centralizer HNN group, double and coset
  wreath over a subgroup pair of `SL_2(Z[1/S])` is hyperlinear, in particular `G_2`.
  - Then `SL_2(Z[1/2])` is not flexibly HS-stable.
  - The SL2 half of `arithmetic-pair-is-not-relatively-embeddable` fails.
  - Every SL2 pair-transfer route to `non-hyperlinear-group` listed in (K4) of
    `sl2-pair-witnesses-need-non-ce-f2xf2-action` has a false prerequisite.
  - Every torsion-free lattice in a product of two trees is hyperlinear.
- **If false.** There is an essentially free action of `F_2 × F_2` with a non-CE crossed product.
  - That is a non-CE relation factor of a group with the Haagerup property and without (T).
  - It is not yet a non-hyperlinear group: the `algebraic-envelope-principle` and
    measure-full-group compilers need extra structure on the action.

Every p.m.p. action of `F_2` has a CE crossed product.
- After a product with the Bernoulli shift, the action is essentially free, and the crossed
  product sits inside the new one trace-preservingly.
- The new orbit relation is treeable, so its von Neumann algebra is CE by
  `non-ce-relation-is-not-treeable`.

So the open problem is only how to combine two commuting free-group actions.

## Attempts

- **Treeability (dies at step 1).** For an essentially free action, the orbit relation of
  `F_2 × F_2` has `β_2^(2) = β_2^(2)(F_2 × F_2) = β_1^(2)(F_2)^2 = 1 ≠ 0`. This uses Künneth
  and Gaboriau's theorem that `ℓ^2` Betti numbers of a free action equal those of its orbit
  relation. Treeable relations have
  `β_2^(2) = 0`, so the relation is not treeable. The route through
  `non-ce-relation-is-not-treeable` does not apply.
- **Iterated crossed product (dies at the lifting step).** Write
  `M = (L^∞(X) ⋊ F_2^(1)) ⋊ F_2^(2) = N ⋊ F_2^(2)`. The algebra `N` is CE by the free-group case.
  - Because `F_2^(2)` is free, `M` is CE as soon as some trace-preserving embedding
    `ι : N → R^ω` admits unitaries `u_1, u_2 ∈ R^ω` with `u_i ι(x) u_i^* = ι(α_i(x))` for all
    `x ∈ N`. Tensoring the `u_i` with free Haar unitaries then fixes the trace. Such unitaries
    exist iff `ι` and `ι ∘ α_i` are unitarily conjugate in `R^ω`,
    which is the analogue of `finitary-extension-ce-iff-action-lifts-to-normalizer`.
  - When the normal factor is amenable, uniqueness of embeddings up to conjugacy supplies the
    `u_i`. That is exactly how `amenable-by-virtually-free-twisted-crossed-products-are-ce` goes.
  - Here `N ⊇ L(F_2)` is not amenable. By Jung's characterization of amenability, `N` has
    embeddings that are not conjugate to each other. One would need a single embedding `ι` fixed,
    up to conjugacy, by both `α_1` and `α_2` at once. No mechanism for choosing it is known.
  - This is the step where the attack dies.
- **Coupling to `SL_2(Z[1/2])`.** By `sl2-pair-witnesses-need-non-ce-f2xf2-action` this hole is
  equivalent to `SL_2(Z[1/2]) ∈ 𝒜`. Attacks from the arithmetic side (congruence
  representations, the `(τ)` gap) cannot see the invariant, so they are not expected to help.
