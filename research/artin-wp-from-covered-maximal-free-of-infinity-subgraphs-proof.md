---
rg: 2
id: artin-wp-from-covered-maximal-free-of-infinity-subgraphs-proof
kind: route
title: Split each maximal free-of-infinity subgraph as a direct product, solve each factor, and transfer along infinite labels
target: artin-wp-from-covered-maximal-free-of-infinity-subgraphs
requires:
  - artin-word-problem-reduces-to-free-of-infinity-graphs
  - known-artin-classes-have-solvable-word-problem
  - no-a3-b3-and-cyclic-type-artin-groups-have-solvable-wp
---

**Lemma (products).** Let `Λ` be a Coxeter graph on a finite set
`X = X_1 ⊔ ⋯ ⊔ X_k`, with `m_st = 2` whenever `s ∈ X_i`, `t ∈ X_j` and `i ≠ j`. Write
`Λ_i = Λ_{X_i}`. Then `A_Λ ≅ A_{Λ_1} × ⋯ × A_{Λ_k}`.

Let `w` be a word over `X^{±}`, and let `w_i` be the word obtained by deleting the letters
not in `X_i^{±}`. Then `w = 1` in `A_Λ` if and only if `w_i = 1` in `A_{Λ_i}` for every
`i`. So if every `A_{Λ_i}` has solvable word problem, so does `A_Λ`.

*Proof.*
1. **The projections.** Define `p_i` on generators by `p_i(s) = s` for `s ∈ X_i` and
   `p_i(s) = 1` otherwise. It respects each defining relation
   `prod(s,t; m_st) = prod(t,s; m_st)`:
   - if `s, t ∈ X_i`, the image is a relation of `Λ_i`;
   - if exactly one of them lies in `X_i`, say `s`, then `m_st = 2` and the image is
     `s = s`;
   - if neither lies in `X_i`, the image is `1 = 1`.

   So `p_i: A_Λ → A_{Λ_i}` is a homomorphism. Put `p = (p_1, …, p_k)`.
2. **The inclusions.** The map `q_i: A_{Λ_i} → A_Λ` with `s ↦ s` is a homomorphism,
   since the relations of `Λ_i` are relations of `Λ`. For `i ≠ j`, the images of `q_i`
   and `q_j` commute, because their generators do.
3. **The product map.** Define `q(g_1, …, g_k) = q_1(g_1) ⋯ q_k(g_k)`. Reordering the
   commuting factors gives `q(gh) = q(g) q(h)`, so `q` is a homomorphism.
4. **Mutually inverse.** For `s ∈ X_i`, `p(s)` is the tuple with `s` in position `i` and
   `1` elsewhere, and `q` sends this tuple back to `s`. So `q ∘ p` fixes the generators of
   `A_Λ`. Also `p ∘ q` fixes these tuples, which generate the product. Hence `p` and `q`
   are inverse isomorphisms.
5. **The word criterion.** Finally, `p_i(w)` is represented by `w_i`. So `w = 1` if and
   only if every `w_i = 1`. ∎

**Assembly.** Let `X ⊆ S` be maximal free of infinity, and take the partition
`X = X_1 ⊔ ⋯ ⊔ X_k` from the hypothesis.

1. Each `A_{Γ_{X_i}}` has solvable word problem:
   - by `known-artin-classes-have-solvable-word-problem` when `Γ_{X_i}` is right-angled,
     spherical, irreducible euclidean, of type FC, of large type, of dimension at most 2
     or of rank three;
   - by `no-a3-b3-and-cyclic-type-artin-groups-have-solvable-wp` in the two remaining
     cases.
2. By the lemma with `Λ = Γ_X`, `A_{Γ_X}` has solvable word problem.
3. Since `X` was arbitrary, `artin-word-problem-reduces-to-free-of-infinity-graphs` shows
   that `A_Γ` has solvable word problem. ∎
