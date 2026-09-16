---
rg: 2
id: bnsr-invariants-are-detected-on-finite-index-subgroups
kind: claim
title: "If H has finite index in a group G of type F_n, restriction embeds S(G) in S(H) and [chi] lies in Sigma^m(G) iff [chi|_H] lies in Sigma^m(H), for m <= n"
---

Let `G` be a group of type `F_n` (`1 ≤ n ≤ ∞`) and `H ≤ G` a subgroup of
finite index. Then:

1. `H` is of type `F_n`.
2. For every non-trivial character `χ: G → R`, the restriction `χ|_H` is
   non-trivial, and `[χ] ↦ [χ|_H]` is a well-defined injective map
   `res: S(G) → S(H)`.
3. For every `m` with `1 ≤ m ≤ n` and every non-trivial `χ`,
   `[χ] ∈ Σ^m(G)` if and only if `[χ|_H] ∈ Σ^m(H)`.

`res` is usually not surjective, since `H` can have more characters than `G`.

**Novelty.** None is claimed. This is a standard fact, and Zaremsky uses it in
this form for `P_n ≤ B_n` (arXiv:1507.08597v1, §3). The route gives a
self-contained proof. The only import is that `Σ^m` does not depend on the
admissible complex and height function chosen, which is part of the
definition as stated in the sources.

**Consequences for `G` of type `F_∞`.**

- If `Σ^m(G) ⊋ Σ^{m+1}(G)`, then `Σ^m(H) ⊋ Σ^{m+1}(H)`: a class in
  `Σ^m(G) \ Σ^{m+1}(G)` restricts to a class in `Σ^m(H) \ Σ^{m+1}(H)`. So if
  `G` answers Zaremsky Problem 1.18 affirmatively, so does every finite-index
  subgroup of `G`.
- If `Σ^m(H) = Σ^k(H)` for all `m ≥ k`, then `Σ^m(G) = Σ^k(G)` for all
  `m ≥ k`.

Proof: `bnsr-invariants-are-detected-on-finite-index-subgroups-proof`.
