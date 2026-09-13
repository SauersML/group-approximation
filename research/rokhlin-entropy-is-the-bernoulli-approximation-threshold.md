---
rg: 2
id: rokhlin-entropy-is-the-bernoulli-approximation-threshold
kind: claim
title: Rokhlin entropy is the least base entropy of a Bernoulli measure approximated by shift models of the action, and approximate Bernoulli classification is equivalent to an infinite Rokhlin supremum
distinct_from:
  rokhlin-entropy-is-the-largest-partition-bounded-invariant: that characterizes Rokhlin entropy among invariants bounded by generating partitions; this characterizes it as the threshold of weak* approximation of Bernoulli measures by isomorphic shift models, and derives the approximate form of Bernoulli classification.
  bernoulli-shift-entropy-classifies-for-every-group: that is the open exact classification; this proves that its approximate form is equivalent to INF(G), so on a group with finite supremum the root is a non-closure statement.
  nontrivial-bernoulli-shifts-are-weakly-equivalent: that is weak equivalence of all nontrivial Bernoulli shifts; this uses generating approximations, which are models of the whole action and separate base entropies when the supremum is infinite.
---

Let `G` be a countably infinite group and `G ↷ (X, μ)` a free ergodic p.m.p. action.
For a finite set `L` with probability vector `λ`, let `M_L(X)` be the set of
`ν ∈ E_G(L^G)` such that `G ↷ (L^G, ν)` is isomorphic to `X`. Write
`s = h^Rok_sup(G)`.

**Theorem.**
1. If `h^Rok_G(X) < H(λ)`, then `λ^G` lies in the weak* closure of `M_L(X)`.
2. If `λ^G` lies in the weak* closure of `M_L(X)`, then
   `h^Rok_G(X) ≤ h^Rok_G(L^G, λ^G) = min(H(λ), s)`.
3. Hence `h^Rok_G(X) = inf { H(λ) : L finite, λ^G ∈ closure of M_L(X) }`. Rokhlin
   entropy is the approximation threshold of Bernoulli measures by shift models of `X`.

**Corollary (approximate classification).** Let `(L, λ)` and `(K, κ)` be finite
bases with `H(λ), H(κ) > 0`.
- If `min(H(κ), s) < H(λ)`, then `λ^G` lies in the closure of `M_L(K^G)`.
- If `λ^G` lies in the closure of `M_L(K^G)`, then `min(H(κ), s) ≤ min(H(λ), s)`.

Say that **AINV(G)** holds when `λ^G` is not in the closure of `M_L(K^G)` for all
finite bases with `H(λ) < H(κ)`. Then:
- AINV(G) ⟺ INF(G), where INF(G) is `s = ∞`;
- AINV(G) ⟹ INV(G), the classification asserted for `G` by
  `bernoulli-shift-entropy-classifies-for-every-group`.

**Reading for the root.** Suppose `s < ∞`. Then Bernoulli shifts with finite base
entropies above `s` approximate each other's Bernoulli measures in both directions, by
shift models isomorphic to the action. Over such a group, the root says exactly that
these approximations never close: `λ^G ∉ M_L(K^G)`. So on every group, a proof of
INV(G) is either a proof of INF(G) or a proof that such approximations cannot close.
`semicontinuous-invariants-blind-above-rokhlin-supremum` records which invariants
cannot give the second kind of proof.

**Credit and novelty.** Items 1 and 2 are immediate from Seward's Corollary 6.1 and
Lemma 6.2 (`seward-approximate-bernoulli-models-and-semicontinuity`). The formulation
as a threshold, and the equivalence AINV ⟺ INF, were not found in arXiv:1501.03367v4
or arXiv:1805.08279v1. Krieger III (arXiv:1705.09707) was not checked.

**ESTABLISHED 2026-09-12** by [[rokhlin-entropy-is-the-bernoulli-approximation-threshold-proof]].
