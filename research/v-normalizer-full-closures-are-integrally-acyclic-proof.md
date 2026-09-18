---
rg: 2
id: v-normalizer-full-closures-are-integrally-acyclic-proof
kind: route
title: The outer-class map makes the germ groupoid an extension of Q by the Cuntz groupoid, whose homology vanishes, and Li's vanishing corollary then applies
target: v-normalizer-full-closures-are-integrally-acyclic
requires:
  - v-normalizer-rsgs-contract-iff-finite-outer-order
  - v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz
artifacts:
  - research/artifacts/gq-gq-infinite-primes-out-v-reading.md
---

**Setup.** Let `O` be the groupoid of germs of `V`. It is the SFT groupoid of the full one-sided
2-shift, and its reduced C*-algebra is `O_2`.

**Step 1: `ρ : G_Q → Q`.** Send the germ `[g, x]` to the class of `g` in `Out(V)`.
- **Well defined.** If `[g, x] = [g', x]`, then `g^{-1}g'` agrees with the identity near `x`. By the
  Lemma in `v-normalizer-rsgs-contract-iff-finite-outer-order-proof`, an element of `N(V)` that
  agrees with an element of `V` on a cone lies in `V`. That Lemma uses only that the element is
  nontrivial in `O_2`, not that it has infinite order. So `g^{-1} g' ∈ V`.
- **The map.** `ρ` is a continuous (locally constant) homomorphism onto `Q`. Its kernel is `O`.
- **Consequences.** `G_Q` is the disjoint union of the clopen sheets `ρ^{-1}(q)`, each a translate
  of `O`. So it is a Hausdorff, second countable, ample groupoid on the Cantor space, and
  `Q ≤ Out(V)` is countable.

**Step 2: the skew product is homologically similar to `O`.** In Matui's skew product
`G_Q ×_ρ Q`, let `F = G_Q^(0) × {e}`. Then `(G_Q ×_ρ Q)|F = {(g, e) : ρ(g) = e} ≅ O`. `F` is
clopen and full: a unit `(x, γ)` is joined to `F` by `(g, e)` for any germ `g` at `x` with
`ρ(g) = γ`, and such a germ exists because every class in `Q` is represented by a homeomorphism.
The unit space is σ-compact and totally disconnected. So by Matui's Theorem `reduction` (2) and
Proposition `homosim`, `H_q(G_Q ×_ρ Q) ≅ H_q(O)` for all `q`.

**Step 3: `H_*(O) = 0`.** By Matui's Theorem `CKHomology`, for an SFT groupoid
`H_0 ≅ K_0(C*_r)`, `H_1 ≅ K_1(C*_r)` and `H_n = 0` for `n ≥ 2`. Here `C*_r(O) = O_2`, and
`K_0(O_2) = K_1(O_2) = 0` (Cuntz). So `H_q(O) = 0` for all `q`.

**Step 4: `H_*(G_Q) = 0`.** Matui's Theorem `LHS` (1), applied to `ρ`, gives
`E^2_{p,q} = H_p(Q, H_q(G_Q ×_ρ Q)) ⇒ H_{p+q}(G_Q)`. By Steps 2–3 every `E^2` term is 0. This is item 1.
For `Q = ⟨t⟩` infinite cyclic, Theorem `LHS` (2) applied to `O ⋊_t Z ≅ G_Q`
(`v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz`, item 1) gives the same result.

**Step 5: Li's corollary.**
- **Hypotheses.** `G_Q` is ample, its unit space is the Cantor space (so it has no isolated points),
  and it is minimal because it contains `O`.
- **Purely infinite minimal**, in Li's sense (TeX l. 804). Given compact open `U` and a nonempty
  compact open `V'`, choose a cone `C_w ⊆ V'`. The germs of the prefix map `x ↦ wx`, which lie in
  `O`, form a compact open bisection from `C` into `C_w`. Restricting it to `U` gives a bisection
  with source `U` and range inside `V'`. Li notes that purely infinite minimal groupoids have
  comparison.
- **Conclusion.** Corollary `introcor:Vanish` says: "if `H_*(G) ≅ {0}` for all `* ≥ 0`, then
  `F(G)` is integrally acyclic ... and `F(G) = D(G)`". Here `F(G_Q)`, the group of full compact open
  bisections, is `[[Γ_Q]]`. This is item 2. ∎
