---
rg: 2
id: fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap-proof
kind: route
title: Identify the ultraproduct with the Bernoulli class, compute its cost through a free standard factor, and read off the combinatorial cost
target: fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap
requires:
  - cgdls-ultraproduct-cost-equals-combinatorial-cost
  - burton-kechris-weak-class-limits-are-ultraproducts
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - cost-is-constant-on-weak-equivalence-classes
---

Notation is as in the target. "CGdlS item k" refers to the numbered items of
`cgdls-ultraproduct-cost-equals-combinatorial-cost`. C(s) is finite, since C(s) ≤ |S|.

**Step 1: b_u ≃ s.** F̃R carries the relative topology of Ã, so b̃_n → s̃ in Ã. By
`burton-kechris-weak-class-limits-are-ultraproducts`, ∏_n b_n/u ≃ s. In statistics form,
C_{n,k}(b_u) = C_{n,k}(s) for all n,k.

**Step 2: b_u is essentially free.** Fix g ≠ e. Each b_n is a standard action, so it is
realizable (CGdlS item 2), and the bisection of g in b_u is [b_n(g)]_u. By Lemma 2.43,
Fix(b_u(g)) = [Fix(b_n(g))]_u up to null sets. By Theorem 2.29(1), its measure is
lim_u μ(Fix(b_n(g))) = 0, because b_n is free. Γ is countable, so b_u is essentially free.

**Step 3: C(b_u) = C(s).** The groupoid of b_u is an ultraproduct of realizable graphed
groupoids, so it is realizable (CGdlS item 2). CGdlS item 4 gives a free standard factor
(G′, S′) with C(G′) = C(b_u). By the reading recorded under item 4, G′ is the action groupoid
of an essentially free p.m.p. action y of Γ on a standard space (Y,ν), and y is a factor of b_u
through a measure-preserving equivariant map π : X_u → Y. Y is non-atomic because Γ is infinite
and y is free.

- *y ≼ s.* Let B_0,…,B_{k−1} be a Borel partition of Y. The sets A_i = π^{−1}(B_i) form a
  μ_u-measurable partition of X_u, and μ_u(γ(A_i) ∩ A_j) = ν(γ(B_i) ∩ B_j) for all γ, by
  equivariance and measure preservation. So every matrix M^{B̄}_{n,k}(y) is a matrix of b_u.
  Hence C_{n,k}(y) ⊆ C_{n,k}(b_u) = C_{n,k}(s) by Step 1, that is, y ≼ s.
- *s ≼ y.* y is free, so `abert-weiss-free-actions-weakly-contain-bernoulli` gives this.

So y and s are weakly equivalent free actions of the finitely generated group Γ.
`cost-is-constant-on-weak-equivalence-classes` gives C(y) = C(s), hence C(b_u) = C(G′) = C(s).

As a consistency check, Theorem 4.2 (CGdlS item 5) independently gives C(b_u) ≤ C^*(Γ) = C(s)
for the essentially free b_u.

**Step 4: part (a).** Theorem 4.2 (CGdlS item 5) gives C(b_u) = cC_u((b_n)n). With Step 3,
cC_u((b_n)n) = C(s).

**Part (b).** By Definition 3.11 (CGdlS item 3) with Φ_n = S for all n,
cC_u((b_n)n) = inf_{M∈N^N} lim_u C_M(b_n). This equals C(s) by (a), so lim_u C_M(b_n) ≥ C(s)
for every M. For the liminf, choose n_1 < n_2 < … with C_M(b_{n_j}) → liminf_n C_M(b_n), and a
non-principal u containing {n_j : j ∈ N}. The first statement applied to this u gives
liminf_n C_M(b_n) ≥ C(s).

**Part (c).**
- *1 ⇒ 2.* C(s) ≤ liminf_n C(b_n) ≤ lim_u C(b_n) ≤ C(b_u) = C(s), using Theorem 4.2 and (a).
  So equality holds throughout.
- *2 ⇒ 1.* Choose u containing a subsequence along which C(b_n) → liminf_n C(b_n), as in (b).
  Then liminf_n C(b_n) = lim_u C(b_n) = C(b_u) = C(s).
- *2 ⇒ 3.* Given ε > 0, (a) gives inf_M lim_u C_M(b_n) = C(s) = lim_u C(b_n). So some M has
  lim_u C_M(b_n) ≤ lim_u C(b_n) + ε.
- *3 ⇒ 2.* For each ε > 0 there is M with
  C(b_u) = cC_u((b_n)n) ≤ lim_u C_M(b_n) ≤ lim_u C(b_n) + ε.
  So C(b_u) ≤ lim_u C(b_n), and Theorem 4.2 gives the reverse inequality.

**Part (d).** Suppose that for some M and some η < δ, the set of n for which b_n has a graphing
Ψ_n with C(Ψ_n) ≤ C(b_n) + η and Ψ_n M-coarsely equivalent to S belongs to u. On that set,
C_M(b_n) ≤ C(b_n) + η by Definition 3.8. So lim_u C_M(b_n) ≤ C(s) − δ + η < C(s), which
contradicts (b).

**Consequence paragraph of the target.**
- `fpbs-bernoulli-lower-bound-from-weak-class-lsc-approximation` shows that the Bernoulli lower
  bound is equivalent to the conjunction of `fpbs-bernoulli-weak-class-cost-lsc` and
  `fpbs-bernoulli-weak-class-cheap-approximability`. Part (c) replaces the first conjunct by
  (c3).
- For finitely generated Γ, fixed price is the Bernoulli lower bound, because C(a) ≤ C(s) for
  free a. If cheap approximability holds and fixed price fails, the first conjunct fails. Then
  (c), 1 ⇒ 2 in contrapositive, gives a sequence and an ultrafilter with
  C(b_u) > lim_u C(b_n).
