---
rg: 2
id: fpbs-weakly-mixing-half-is-fixed-price-without-t
kind: claim
title: For a finitely generated group without property (T), cost preservation along relatively weakly mixing extensions is equivalent to fixed price
distinct_from:
  fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation: that shows P_c and P_w together give cost preservation along every free factor; this shows P_w alone already gives fixed price when G lacks (T), so the split is not a decomposition on that class.
  fpbs-relatively-weakly-mixing-extensions-preserve-cost: that is the open statement P_w itself; this is the equivalence of P_w with fixed price for non-(T) groups, which settles nothing about either side.
  fpbs-factor-invariance-equals-fixed-price: that identifies cost invariance under all free factor maps with fixed price; this identifies invariance under the relatively weakly mixing ones, and even under the single projection a_w x b -> b, with fixed price when G lacks (T).
  fpbs-bernoulli-noise-does-not-change-cost: that gives C(a x b) = C(a) for the projection a x b -> a with Bernoulli fibre; this uses it together with the other projection a_w x b -> b, whose fibre is the weakly mixing maximum.
artifacts:
  - research/artifacts/fpbs-weakly-mixing-half-is-fixed-price-2026-09-17.md
---

**ESTABLISHED.** Let G be an infinite finitely generated group without property (T). Let a_w be
a weakly mixing action that is weakly equivalent to the maximum a_∞,G, and let b be a Bernoulli
shift. Then a_w is free, and the following are equivalent.

1. G has fixed price.
2. P_w(G): every relatively weakly mixing extension V → W of free p.m.p. G-actions has
   C(V) = C(W). Relative weak mixing is Definition 6.1 of Jamneshan, read on the functions f with
   E(|f|²|W) ∈ L²(W).
3. The single relatively weakly mixing extension a_w × b → b preserves cost.

So P_w(G) implies P_c(G) for every such G.

For every finitely generated G, with or without (T), P_w(G) also gives C(w) = C(b) for every free
weakly mixing w.

The proof is in artifact Section 3. By `burton-kechris-maximum-action-weakly-mixing-without-t`, a_w
exists. It is free because b ≼ a_w and freeness is upward closed. By
`weakly-mixing-fibre-products-are-relatively-weakly-mixing`, a_w × b → b is relatively weakly
mixing. Now (3) gives C(a_w × b) = C(b), and `fpbs-bernoulli-noise-does-not-change-cost` gives
C(a_w × b) = C(a_w). Every free a has a ≼ a_w, so C(a) ≥ C(a_w) by monotonicity. By Bernoulli
maximality, C(a) ≤ C(b_0) = C(a_w) for a Bernoulli b_0 of maximal cost.

**Scope label.** This is a reformulation, not a weakening. It proves no cost equality. Its
content is that P_w carries the whole fixed price problem on the non-(T) class, while P_c is
redundant there. The Furstenberg-Zimmer split has independent content only for Kazhdan groups, and
there `fpbs-kazhdan-weak-containment-preserves-weak-mixing` limits what P_w can reach by
weak-containment transfer.
