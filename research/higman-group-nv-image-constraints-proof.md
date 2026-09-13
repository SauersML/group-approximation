---
rg: 2
id: higman-group-nv-image-constraints-proof
kind: route
title: The smallest-prime descent kills finite-order images, the quotient structure of Z[1/2] ⋊ Z makes infinite-order pairs faithful, and the nV periodic-set and entropy theorems apply to each proper-power relation of the cycle
target: higman-group-images-in-nv-force-zero-entropy-bs12-cycles
requires:
  - bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets
  - brin-thompson-proper-power-conjugates-have-zero-entropy
---

Notation as in the target. Indices are taken mod 4. Iterating the relation gives
`γ_i^m γ_(i+1) γ_i^-m = γ_(i+1)^(2^m)` for `m ≥ 0`.

**Step P1 (finite order kills the image).**
- **Spreading.** If `γ_j` has order `n_j < ∞`, taking `m = n_j` gives
  `γ_(j+1) = γ_(j+1)^(2^(n_j))`, so `γ_(j+1)` has finite order. Going round the
  cycle, all four `γ_i` have finite orders `n_i`.
- **Descent.** Suppose `n_(i+1) > 1`.
  - `γ_(i+1)` and `γ_(i+1)^2` are conjugate, so they have the same order, and
    `n_(i+1)` is odd.
  - From `γ_(i+1) = γ_(i+1)^(2^(n_i))` we get `n_(i+1) | 2^(n_i) - 1`.
  - Let `p` be the least prime dividing `n_(i+1)`, so `p ≥ 3`. Then
    `2^(n_i) ≡ 1 (mod p)`, so `r = ord_p(2)` divides `n_i`. Since `p ≥ 3`,
    `r ≥ 2`, and `r | p - 1`, so `r < p`.
  - Hence `n_i > 1`, and the least prime `q_i` dividing `n_i` satisfies
    `q_i ≤ r < p = q_(i+1)`.
- **Contradiction.** If some `n_i > 1`, this applies around the whole cycle and
  gives `q_0 < q_1 < q_2 < q_3 < q_0`. So every `n_i = 1`, and `ψ` is trivial.
  This is Higman's smallest-prime argument, reproduced here.

**Step P2 (Baumslag--Solitar pieces).**
- **Model.** Let `G = Z[1/2] ⋊ Z` with `(r,j)(r',j') = (r + 2^j r', j + j')`.
  Put `s = (1,0)` and `u = (0,1)`, so `u s u^-1 = (2,0) = s^2`.
- **Normal form.** In `BS(1,2)`, `s^m u^(-a) = u^(-a) s^(m 2^a)` for `a ≥ 0`. So
  the set of words `u^(-k) s^m u^j` with `k, j ≥ 0` is closed under right
  multiplication by `u^(±1)` (absorb negative `j` into `k`) and by `s^(±1)`
  (`u^j s^(±1) = s^(±2^j) u^j`). So it is all of `BS(1,2)`.
- **Isomorphism.** The homomorphism `BS(1,2) → G` sends `u^(-k) s^m u^j` to
  `(2^(-k) m, j - k)`.
  - It is onto, because every dyadic rational is `2^(-k) m` with `k ≥ 0`.
  - It is injective: the image is trivial only when `j = k` and `m = 0`, and
    then the word is `1`.
- **Quotients.** Let `N ⊴ G` and `A = Z[1/2] × {0}`, and suppose the image of `s`
  in `G/N` has infinite order.
  - If `(r,0) ∈ N` with `r ≠ 0`, conjugating by `(0,j)` gives `(2^j r, 0) ∈ N`.
    For suitable `j ≥ 0` this is `s^m` with `m ≠ 0`, a contradiction. So
    `N ∩ A = 0`.
  - If `N ≠ 1`, then since `N ∩ A = 0`, `N` contains some `(q,k)` with `k ≠ 0`.
    Conjugating `s` by `(q,k)` gives `(2^k, 0)`, so `[(q,k), s] = (2^k - 1, 0)`.
    That lies in `A` because `A` is normal, and in `N` because `N` is normal. It
    is nonzero because `k ≠ 0`, contradicting `N ∩ A = 0`. So `N = 1`.
- **Conclusion.** For nontrivial `ψ`, P1 makes `γ_(i+1)` of infinite order. The
  map `u ↦ γ_i`, `s ↦ γ_(i+1)` respects the relation, so it factors through a
  quotient of `BS(1,2)` in which `s` has infinite order. By the quotient lemma
  that quotient is `BS(1,2)` itself.

**Step P3 (periodic structure).**
- Apply `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets` with
  `g = γ_(i+1)`, `f = γ_i`, `k = 1`, `l = 2`. Its items 1, 2 and 4 give the
  exponent, local periodicity and growth conclusions. Item 3 gives a nonempty
  closed `γ_(i+1)`-invariant core, since `γ_(i+1)` has infinite order.
- **Invariance under `γ_i`.** For a homeomorphism `f`, `x` is `g`-periodic iff
  `fx` is `fgf^-1`-periodic. Here `f g f^-1 = g^2`, and `g^2` has the same
  periodic points as `g`. So `γ_i Per(γ_(i+1)) = Per(γ_(i+1))`, and the
  complement `K(γ_(i+1))` is `γ_i`-invariant.

**Step P4 (zero entropy).** Item 3 of
`brin-thompson-proper-power-conjugates-have-zero-entropy`, with `g = γ_(i+1)`,
`f = γ_i`, `k = 1`, `l = 2`, gives `h(γ_(i+1)) = 0` for every `i`. By item 4 of
that claim, the baker map has positive entropy, so it is none of the `γ_i`.

**Corollary.** A nontrivial `ψ` gives `BS(1,2) ≤ nV` by P2. So if `BS(1,2)` does
not embed in `nV`, every `ψ` is trivial. ∎
