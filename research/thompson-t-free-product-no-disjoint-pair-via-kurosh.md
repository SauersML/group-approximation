---
rg: 2
id: thompson-t-free-product-no-disjoint-pair-via-kurosh
kind: route
title: A Z^2 in a free product lies in a conjugate of a factor, and a conjugate of one of its elements by the other factor generates Z^2 * Z
target: thompson-t-free-product-subgroups-have-no-disjoint-pair
requires:
  - z2-free-z-does-not-embed-in-thompson-v
artifacts:
  - research/artifacts/thompson-t-disjoint-pair-witness-obstructions-2026-09-16.md
---

**Standard inputs, not re-read.**
- (K) Kurosh subgroup theorem: a subgroup of `A * B` is a free product of a free group and
  of intersections with conjugates of `A` and `B`.
- (N) Normal forms: in `A * B`, a product `x_1 ⋯ x_k` with `k ≥ 1`, every `x_i` in
  `A \ {1}` or `B \ {1}`, and consecutive letters from different factors, is nontrivial.
- (TV) `T ≤ V`, stated in the introduction of arXiv:0911.0979v1 ("T ≤ V").

**Proposition.** If `G = A * B` with `A ≠ 1 ≠ B` contains `P ≅ Z^2`, then `G` contains
`Z^2 ∗ Z`.

*Proof.*
1. *`P` lies in a conjugate of a factor.* By (K), `P` is a free product of a free group and
   of groups `P ∩ g C g^(-1)` with `C ∈ {A, B}`. A free product of two nontrivial groups is
   non-abelian by (N), so exactly one of these free factors is nontrivial. It is not free,
   because `Z^2` is not free. So `P ≤ g C g^(-1)`. After conjugating and renaming the
   factors, `P ≤ A`, and `B ≠ 1` still holds.
2. *The companion.* Choose `β ∈ B \ {1}` and `x ∈ P \ {1}`, and put `c = β x β^(-1)`.
3. *Injectivity.* Define `φ : P * ⟨t⟩ → G` by `φ|_P = id` and `φ(t) = c`, where `⟨t⟩ ≅ Z`.
   A nontrivial element outside `P` has reduced form
   `p_0 t^(k_1) p_1 ⋯ t^(k_n) p_n` with `n ≥ 1`, all `k_i ≠ 0`, `p_1, …, p_(n−1) ≠ 1`, and
   `p_0, p_n` possibly trivial. Its image is
   `p_0 · β x^(k_1) β^(-1) · p_1 · β x^(k_2) β^(-1) ⋯ β x^(k_n) β^(-1) · p_n`.
   Every `x^(k_i)` lies in `A \ {1}`, since `x` has infinite order. The letters `β^(±1)` lie
   in `B \ {1}`, and `p_1, …, p_(n−1)` lie in `A \ {1}`. After dropping a trivial `p_0` or
   `p_n`, the word alternates between the factors and has at least 3 letters. So it is
   nontrivial by (N). Elements of `P` map to themselves. So `φ` is injective and
   `⟨P, c⟩ ≅ Z^2 ∗ Z`. ∎

**Proof of the claim.** Let `H ≤ V` with `H ≅ A * B`, `A ≠ 1 ≠ B`, and suppose `Z^2 ≤ H`.
By the Proposition, `Z^2 ∗ Z ≤ H ≤ V`. This contradicts
`z2-free-z-does-not-embed-in-thompson-v`.

For the statement about `T`, let `a, b ∈ T \ {1}` have disjoint supports on `S^1`.
1. They commute: on `supp(a)` the map `b` is the identity and `a` preserves `supp(a)`, and
   symmetrically on `supp(b)`. Both are the identity elsewhere.
2. Both have infinite order. `a` fixes the nonempty set `supp(b)` pointwise, so it has a
   fixed point. Cutting the circle there makes `a` an increasing homeomorphism of `[0, 1]`,
   and such a map of finite order is the identity.
3. If `a^m b^n = 1`, then `a^m = b^(−n)` has support in `supp(a) ∩ supp(b) = ∅`. So
   `a^m = 1 = b^n` and `m = n = 0`.

So `⟨a, b⟩ ≅ Z^2`, and the first part applies by (TV). ∎
