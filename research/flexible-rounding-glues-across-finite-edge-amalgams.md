---
rg: 2
id: flexible-rounding-glues-across-finite-edge-amalgams
kind: claim
title: Flexible HS roundings of the two factors of an amalgam over a finite group glue to a rounding of the amalgam once some finite quotient is injective on the edge group
distinct_from:
  triangle-of-finite-groups-hs-stability-is-edge-matching: that is a triangle of finite groups, where three almost-matching vertex representations must be glued around a cycle and gluing is the whole open content; this is a single edge (a tree), with arbitrary infinite factors, where gluing is always possible after an o(d)-dimensional multiplicity balance.
  flexible-hs-stability-descends-to-retracts-finite-index: that passes flexible stability down to retracts and finite-index subgroups; this passes flexible roundings up from the two factors to the amalgam, element by element, with no stability hypothesis on either factor.
  codense-tau-amalgams-fold-under-flexible-stability: that folds two vertex copies of doubled finite actions using a swap vector; this is the unitary normalized-HS gluing of two independent roundings along a finite edge group by a representation-ring balance and a Mirsky polar correction.
---

**ESTABLISHED** (route `flexible-rounding-finite-edge-amalgam-gluing-proof`; lane proof, unreviewed,
elementary, no priority claimed).

**Setting.** `A` and `B` are groups containing a common finite subgroup `H`, and
`G = A *_H B`. Assume some homomorphism `q : G -> F` to a finite group is injective on `H` (true
whenever `G` is residually finite). Norms `||.||_(2,n)` are normalized by `n`, and `P` is the
co-isometry onto the first `d_n` coordinates.

A sequence of maps `σ_n : S -> U(d_n)`, defined on a subgroup `S`, is **flexibly roundable on `S`** if
there are genuine representations `λ_n : S -> U(D_n)`, `D_n >= d_n`, `D_n/d_n -> 1`, with
`||σ_n(x) - P λ_n(x) P*||_(2,d_n) -> 0` for every `x in S`.

**Theorem.** Let `σ_n : G -> U(d_n)` be maps with `σ_n|_A` flexibly roundable on `A` and
`σ_n|_B` flexibly roundable on `B`. Then there are genuine representations `ρ_n : G -> U(M_n)`,
`M_n/d_n -> 1`, with `||σ_n(x) - P ρ_n(x) P*||_(2,d_n) -> 0` for every `x in A ∪ B`. If moreover
`σ_n` is an asymptotic representation of `G`, this holds for every `x in G`.

**Corollary.** If `A` and `B` are flexibly HS-stable (Dogon, arXiv:2211.10492v3, Definition 1.2),
then so is `G`.

**Mechanism.**
1. The two roundings restrict to genuine representations `θ^A, θ^B` of the finite group `H` that
   are `o(1)`-close in normalized HS. Their multiplicity vectors differ by `o(D_n)`.
2. **Balance.** The difference lies in the finitely generated lattice `L_A + L_B` inside the
   representation ring `R(H)`, where `L_A` and `L_B` are spanned by restrictions of finite-dimensional
   representations of `A` and of `B`. So it is an integer combination of fixed generators, with
   coefficients `O(o(D_n))`. Negative coefficients become genuine summands through the identity
   `a|_H + (a ⊗ (Reg_F|_A ⊖ 1))|_H = |F:H| dim(a) · Reg_H`. This adds genuine summands
   `α_n` on `A` and `β_n` on `B` of dimension `o(d_n)`, after which the restrictions to `H` are
   unitarily equivalent.
3. **Conjugate.** The averaged intertwiner `T = |H|^(-1) Σ_h Θ^A(h) Θ^B(h)*` is `o(1)`-close to `1`.
   Its polar unitary `U`, taken in the commutant, conjugates `Θ^B|_H` onto `Θ^A|_H`. By Mirsky's
   singular-value inequality, `||U - 1||_2 <= 2||T - 1||_2`.
4. **Glue.** `ρ_n = (λ^A ⊕ α_n) *_H U(λ^B ⊕ β_n)U*` is a genuine representation of `G`.

**Where it is used.** `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding` applies it to
the residually finite Cuntz-cone cover `Γ = Δ_+ *_(Δ_0) Δ_-` of
`leavitt-cuntz-cone-halves-have-rf-amalgam-cover`, whose edge group `SL_20(F_2)^2` is finite.

Derivation: `flexible-rounding-finite-edge-amalgam-gluing-proof`.
