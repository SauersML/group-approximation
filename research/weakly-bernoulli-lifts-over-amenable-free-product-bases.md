---
rg: 2
id: weakly-bernoulli-lifts-over-amenable-free-product-bases
kind: claim
title: Over amenable bases and their free products with Z, non-residually-finite central extensions carry liftable actions weakly equivalent to Bernoulli
distinct_from:
  weakly-bernoulli-liftable-actions-force-virtual-splitting: that is the open claim over w-rigid bases; this shows its conclusion fails once rigidity is dropped, even over non-amenable bases without property (T) whose extension is not residually finite.
  gohla-thom-lattices-no-weakly-bernoulli-liftable-action: that proves the negative polarity over one family of property (T) lattices; this gives the positive polarity over non-rigid bases.
  abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center: that constructs the finitely presented amenable group with an invisible central element; this uses it as the base of an extension that lifts weakly Bernoulli actions.
---

**ESTABLISHED (unreviewed)** by [[weakly-bernoulli-lifts-over-amenable-free-product-bases-proof]].

Let `1 -> N -> W -π-> Q -> 1` be an extension of countable groups with `N` finite.
1. **Amenable bases.** If `Q` is infinite and amenable, then for every free p.m.p. `W`-action `X`, for instance
   `[0,1]^W`, the quotient `X/N` is a free liftable `Q`-action weakly equivalent to `[0,1]^Q`.
2. **Free products.** Let `Q = Q_1 * Q_2`, and suppose each `Q_i` is finite, or is infinite and carries almost-lifts
   on its Bernoulli shift for the restricted extension (condition (2) of
   `weakly-bernoulli-lift-iff-bernoulli-almost-lifts`). This holds in particular when `Q_i` is infinite amenable, or
   infinite cyclic. Then `Q` carries a liftable free action weakly equivalent to `[0,1]^Q`.
3. **Non-residually-finite instances.** Let `Γ_p` and its central element `c_p` of order `p` be as in
   `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`, and put `C = <c_p>`.
   - `Q_p = Γ_p / C` is finitely presented, amenable and infinite, and `W = Γ_p` is a central extension that is not
     residually finite.
   - `Q_p * Z` is non-amenable and has no property (T), since it maps onto `Z`. Its central extension
     `Γ_p *_C (C × Z)` is not residually finite.
   - Neither extension splits over any finite-index subgroup.

   By items 1 and 2, both bases carry liftable actions weakly equivalent to Bernoulli.

**Scope.**
- The conclusion of `weakly-bernoulli-liftable-actions-force-virtual-splitting` fails over these bases. So its
  rigidity hypothesis cannot be replaced by non-amenability, by failure of property (T), or by failure of residual
  finiteness of the extension.
- These examples do not touch the claim itself, which assumes a w-rigid base. The Popa-type node needs an infinite
  normal subgroup with relative property (T), and an amenable group has none. For `Q_p * Z` that hypothesis is not
  checked here.
- In each example the persistent class is carried by an amenable subgroup. A positive example whose class is not
  carried in this way is the open target `deligne-sl2-z-1-p-weakly-bernoulli-lift`.

**Remark (not established here).** With Ornstein--Weiss hyperfiniteness, which is not imported in the graph, every
free action of `Q_p` and of `Q_p * Z` has treeable orbit relation. By
`treeable-free-actions-lift-across-finite-normal-extensions`, the Bernoulli shift itself would then lift exactly.

**Model test.**
- Hypothesis side: `Q_p * Z` is a real object that meets every hypothesis. A trivial model, `Z` with the split
  extension `Z × C_2`, also meets them, and there the conclusion is trivial.
- Conclusion side: the non-splitting in item 3 is forced by invisibility of `c_p`. So the examples have content: an
  exact Popa-type obstruction would have to fail for them.
