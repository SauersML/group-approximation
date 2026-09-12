---
rg: 2
id: toeplitz-coefficient-factoring-kills-leavitt-el3-rank-models
kind: claim
title: A rank model of the Leavitt unit group is trivial once, at the Toeplitz defect, it factors through a directly finite coefficient ring
distinct_from:
  leavitt-algebra-has-no-unital-rank-model: that forbids unital ring homomorphisms from the whole Leavitt algebra into rank ultraproducts; this is a group-level statement that forbids group models whose value at the single root element x_12(1 - s0 t0) comes from a coefficient map of any subring containing the Toeplitz pair into any directly finite ring.
  fd-represented-coefficients-violate-two-root-identities: that builds rank models of EL_3(S) violating the two root identities for finitely represented subrings S; this shows such models never assemble into a model of EL_3 of the Leavitt algebra, because once S contains s0 and t0 they kill x_12(1 - s0 t0).
artifacts:
  - research/artifacts/el3-rank-model-toeplitz-assembly-2026-09-12.md
---

**ESTABLISHED** (proof in the artifact, Section 2). Let `R = L_(F_2)(1,2)` and `G = EL_3(R) ≅ R^x`,
and put `e = 1 − s0 t0`. Let `σ : G -> M^x` be a homomorphism into any ring. Suppose there are:
* a unital subring `S ⊆ R` containing `s0` and `t0`;
* a unital ring homomorphism `φ : S -> D` into a directly finite ring `D`;
* a map `ψ : EL_3(D) -> M^x` with `ψ(1) = 1`;

such that `σ(x_12(e)) = ψ(x_12(φ(e)))`. Then `σ` is trivial.

The same conclusion holds for a rank model `σ = lim_ω σ_k` when, for ω-almost all `k`, the value
`σ_k(x_12(e))` agrees up to normalized rank `o(1)` with such a factoring value over some
`S_k ⊇ T`.

**Why.** `φ(t0) φ(s0) = 1` and direct finiteness give `φ(e) = 0`. So `x_12(e)` goes to `1`, and
`x_12(e) != 1` in the simple group `G`.

**Consequence.** Assembling rank models from finitely represented coefficient subrings dies at
`x_12(1 − s0 t0)`, and so does any family that factors at that element through a finite-dimensional
coefficient representation. Every subring over which `x_12(s0)` and `x_12(t0)` are defined contains
the Toeplitz pair. A nontrivial model must give the finitary `SL_fin(F_2)` spanned by the matrix
units `s0^a e t0^b` positive rank displacement through maps that are neither algebra-like nor
monomial (artifact, Section 5).

**Transfer, scoped to the recorded cases** (scope from `gk-vf-linear`, Section 42 of its
verification artifact). The same argument gives triviality for `EL_3(L)` with `L = L_(F_p)(1,2)`,
`p` odd. There `EL_3(L) ≅ L^x` is perfect and simple modulo its central scalars
(`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`). `x_12(e)` is non-central, so `ker σ` is a
non-central normal subgroup and `σ` has abelian image; by perfection `σ` is trivial.

For other `(K, n)` the step needs `EL_3(L_K(1,n))` simple modulo its centre. No node records that,
and `M_3(L_K(1,n)) ≅ L_K(1,n)` holds only when `(n−1) | 2`. So the transfer is not claimed there.
Theorem A's first step, `φ(e) = 0` and hence `σ(x_12(e)) = 1`, holds for every `(K, n)`.
