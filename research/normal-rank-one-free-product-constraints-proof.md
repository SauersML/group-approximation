---
rg: 2
id: normal-rank-one-free-product-constraints-proof
kind: route
title: Push the normal generator through quotients onto abelian, orderable and G * Z targets
target: normal-rank-one-free-products-need-cyclic-abelianization
requires:
  - left-orderable-free-products-have-normal-rank-above-one
  - klyachko-kl-holds-for-torsion-free
  - kervaire-laudenbach-holds-for-hyperlinear
---

**Step 0 (quotients).** If `f: G -> G'` is onto and `G = <<w>>`, then
`G' = <<f(w)>>`. Indeed `f` maps each conjugate `gwg^{-1}` to
`f(g)f(w)f(g)^{-1}`, and every element of `G'` is some `f(g)`.

**(a)** Abelianization preserves free products as direct sums, so
`G^ab ≅ ⊕_i A_i^ab`. By step 0 the image of `w` normally generates `G^ab`. In an
abelian group the normal closure of an element is the cyclic subgroup it
generates, so `G^ab` is cyclic.

**(b)** Suppose `A_1` and `A_2` (after reindexing) have nontrivial left-orderable
quotients `L_1` and `L_2`. Define `f: G -> L_1 * L_2` as the quotient maps on
`A_1` and `A_2` and the trivial map on each `A_i` with `i >= 3`; it is onto. By
step 0, `f(w)` normally generates `L_1 * L_2`. That contradicts
`left-orderable-free-products-have-normal-rank-above-one`.

**(c)** Let `q: A_j -> Z` be onto, and put `H = *_{i≠j} A_i`, which is nontrivial
because `n >= 2`.
- **The map.** Define `f: G -> Z * H` as `q` on `A_j` and the identity on the other
  factors; it is onto. By step 0, `w' = f(w)` normally generates `Z * H`.
- **Exponent sum.** Let `ε: Z * H -> Z` kill `H`. Then `ε(w')` normally generates
  `Z`, so the exponent sum of `w'` in the `Z` letter is `±1`.
- **If `H` is torsion-free.** `klyachko-kl-holds-for-torsion-free` says that for
  torsion-free `G_0` and `deg_t(v) = ±1`, the map `G_0 -> (G_0 * <t>)/<<v>>` is
  injective. So `H` injects into `(Z * H)/<<w'>> = 1`, which is impossible because
  `H` is nontrivial.
- **If `H` is hyperlinear.** `kervaire-laudenbach-holds-for-hyperlinear` covers one
  equation in one variable with augmentation exponent `±1 != 0`; the presentation
  complex `<x | x^{±1}>` has trivial `H_2`. So there are a group `K ⊇ H` and
  `x ∈ K` with `w'(x) = 1`.
  - The homomorphism `Z * H -> K` sending `t ↦ x` and `H ↪ K` kills `w'`, so it
    factors through `(Z * H)/<<w'>> = 1`.
  - Hence `H ↪ K` would be trivial, which is again impossible.
- **Perfectness.** By (a), `⊕_i A_i^ab` is cyclic, and it maps onto `Z` through
  `q`, so it is infinite cyclic.
  - A surjection from `Z` onto `Z` is an isomorphism, so the kernel of
    `⊕_i A_i^ab -> Z` is trivial.
  - That kernel contains `A_i^ab` for every `i ≠ j`, so those factors are perfect.

**Consequences.**
- **Kirby 66.** Take `n = 2` with `A` and `B` torsion-free.
  - By (c), neither factor maps onto `Z`, since the other factor is torsion-free.
  - By (a), `A^ab` and `B^ab` are direct summands of a cyclic group, hence cyclic,
    hence finite. Moreover `Z/m ⊕ Z/n` is cyclic only when `gcd(m,n) = 1`.
  - By (b), at most one factor has a nontrivial left-orderable quotient.
- **Gordon.** The shape in the claim follows from (a), (b) and (c) in the same
  way. A group mapping onto `Z` has `Z` as a left-orderable quotient, which gives
  the first "already holds" item.
- **Non-cyclic abelianization sums.** When two factors have abelianizations with
  non-cyclic direct sum, `⊕_i A_i^ab` has a non-cyclic direct summand, so it is
  not cyclic, and (a) applies. ∎
