---
rg: 2
id: fpbs-sandwich-cost-fox-rank-lower-bound
kind: claim
title: Every relation sandwiched between a subgroup action and a free action of a free group costs at least the von Neumann rank of the subgroup's Fox matrix, so compressed subgroups have action-independent sandwich cost equal to their rank
distinct_from:
  fpbs-free-group-sandwich-cost-is-two: that is the F_2 statement with value 2 for non-cyclic K; this is the general free-group rank bound it is derived from, stated for any finite rank and any finite family of elements.
  fpbs-sandwich-cost-fiber-formula: that prices group-generated and virtually group-generated sandwiches through strong inertness; this bounds every measurable sandwich, with no group or finite-cover structure, through an L2 rank.
  fpbs-finite-coset-sandwich-cost-commensurator-rank: that prices only the finite-coset part Y_fin of a sandwich through an invariant measure on coset sets; this needs no split into finite and infinite coset parts.
  fpbs-amen2-betti-cost-input: that is Gaboriau's inequality C >= 1 + beta_1 for the full orbit relation; the case h = basis of F of this claim recovers C(E_a) >= rk F for free groups, and the claim extends the bound to all intermediate relations.
---

**ESTABLISHED** through `fpbs-sandwich-cost-fox-rank-lower-bound-proof`.

Let `F` be a free group with basis `f_1, …, f_q`, and let `a` be a free
p.m.p. action of `F` on `(X, μ)`. Let `h_1, …, h_p ∈ F` and
`H = ⟨h_1, …, h_p⟩`. Let `A = (∂h_j/∂f_k) ∈ M_{p×q}(Z F)` be the Fox matrix,
so `h_j − 1 = Σ_k A_{jk}(f_k − 1)` in `Z F`. Let `rk(A)` be its von Neumann
rank over `N(F)`: the trace of the left support projection of `A` in
`M_p(N(F))`.

**(1) Rank bound.** Every measurable equivalence relation `E` with

```text
E_{a|H} ⊆ E ⊆ E_a
```

satisfies `C(E) ≥ rk(A)`.

**(2) Compressed subgroups.** Suppose `H` is compressed in `F` and
`h_1, …, h_p` is a basis of `H`. Then `rk(A) = p`. Hence

```text
p^F_H(a) = inf{ C(E) : E_{a|H} ⊆ E ⊆ E_a } = rk H
```

for every free p.m.p. action `a` of `F`. In particular `p^F_H` is constant on
free actions, which is `fpbs-relative-sandwich-cost-bernoulli-lower-bound`
for the pair `(F, H)`.

**(3) Rank-2 subgroups of F_2.** Every rank-2 subgroup of `F_2` is compressed.
Every non-cyclic subgroup contains one. This gives
`fpbs-free-group-sandwich-cost-is-two`
(route `fpbs-free-group-sandwich-cost-is-two-proof`).

**Mechanism.** The proof uses a Fox cocycle `β` on the pseudogroup `[[E_a]]`,
with values in rows over `L(E_a)`. A graphing of `E` factors a truncation of
`A` through the diagonal of its range projections. The rank of that diagonal
is the graphing's cost.

The proof never uses treeability of `E`, a split into coset parts, or any
structure of `E` other than `E ⊆ E_a`. The only input about `H` is
Jaikin-Zapirain's L2-independence, transported from `N(F)` to `L(E_a)` by a
trace-preserving inclusion.
