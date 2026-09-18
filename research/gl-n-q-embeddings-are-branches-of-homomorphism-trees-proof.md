---
rg: 2
id: gl-n-q-embeddings-are-branches-of-homomorphism-trees-proof
kind: route
title: Unions of compatible homomorphisms, correction by automorphisms, reduction mod p
target: gl-n-q-embeddings-are-branches-of-homomorphism-trees
requires:
  - gl-n-q-embeddings-detected-by-nontrivial-homomorphisms
  - gl-n-q-targets-are-cofinal-in-n
  - elementary-groups-over-polynomial-s-integers-are-fp
---

**The chain.** Over a field `SL_m = E_m`, and each `e_ij(q)` lies in
`E_m(Z[1/k!])` once `k!` is divisible by the denominator of `q`. Since
`k! | (k+1)!`, the groups `H_k = E_m(Z[1/k!])` increase, and their union is
`E_m(Q) = SL_m(Q)`.

**(1).**
- A branch `(ψ_k)` of `T_S` is a compatible family, so its union is a
  homomorphism `ψ: SL_m(Q) -> S` with `ψ(e_12(1)) != 1`. For odd `m` it is
  injective by item (4) of `gl-n-q-embeddings-detected-by-nontrivial-homomorphisms`.
- Conversely, the restrictions of an embedding form a branch, since
  `e_12(1) ∈ H_1`.
- **Computability.** `elementary-groups-over-polynomial-s-integers-are-fp`
  with `k = 0` and `n = m >= 4` makes each `H_k` finitely presented. A finite
  presentation of `H_k`, and words for the generators of `H_(k-1)` in those of
  `H_k`, can be computed from `k`: the generators are elementary matrices, and
  equalities in `SL_m(Z[1/k!])` are decidable by matrix arithmetic. So
  membership of a tuple of words in level `k`, and the parent relation, reduce
  to finitely many instances of the word problem of `S`.

**(2).** Choose a class `c_k ∈ C_k` for each `k` with `c_(k+1)` restricting to
`c_k`. This is possible by Konig's lemma: the finite nonempty sets `C_k`, with
restriction maps `C_(k+1) -> C_k`, have a nonempty inverse limit. Choose
representatives `φ_k`, and `γ_k ∈ A` with `φ_(k+1)|H_k = γ_k ∘ φ_k`.
- Put `α_1 = id` and `α_(k+1) = α_k ∘ γ_k^-1`.
- Then `ψ_k = α_k ∘ φ_k` is an embedding, and
  `ψ_(k+1)|H_k = α_k γ_k^-1 γ_k φ_k = ψ_k`.
- So `⋃ ψ_k` embeds `H`. Nothing about `SL_m` was used.

**(3).** By the survey (arXiv:2306.16356v3, Theorem 4.3(1)), `V` contains
every finite group. For `k >= 1` pick a prime `p > k`. Reduction mod `p` is a
homomorphism `SL_m(Z[1/k!]) -> SL_m(F_p)`, because `k!` is invertible mod `p`,
and it sends `e_12(1)` to `e_12(1) != 1`.
- Compose it with an embedding `SL_m(F_p) -> S`; this is a level-`k` vertex of
  `T_S`.
- If `T_V` had a branch, (1) would embed `SL_m(Q)`, and hence
  `(Q,+) = {e_12(q)}`, in `V`. That contradicts Higman (survey Theorem 4.4; root
  O3).

**(4).**
- By (1) and `gl-n-q-embeddings-detected-by-nontrivial-homomorphisms`, the root
  holds iff for infinitely many odd `m` some finitely presented simple `S` has a
  branch in `T_S`. The cofinality node gives monotonicity in `m`, which yields
  the `m_0` form of the negation.
- There are countably many finite presentations. A branch is a function
  `N -> (tuples of words)`, so "some `T_S` has a branch" is `Σ^1_1`, and its
  negation is `Π^1_1`.
- The remarks on refutation restate (3). A vertex at level `k` exists as soon
  as `S` contains `SL_m(F_p)` for some prime `p > k`.
