---
rg: 2
id: bauer-tracially-divisible-unit-gives-bounded-rank-density
kind: claim
title: On a Bauer trace simplex, a tracially divisible unit gives near projections of every continuous trace profile
distinct_from:
  ultrapower-comparison-with-rank-density-divides-projections: that assumes projection comparison and bounded rank density and divides projections; this assumes neither and derives bounded rank density from divisibility of the unit alone.
  rank-density-is-quadratic-trace-selection: that proves rank density equivalent to quadratic trace selection in any unital algebra; this shows that on Bauer simplices the constant profiles 1/N generate every continuous profile.
  bauer-uniform-gamma-iff-trivial-tracial-bundle: that identifies uniform Gamma with triviality of the strict closure; this uses only the central copy of C(K) in the strict closure and needs no centrality of the divided unit.
  stw99-problem-xxviii-tracial-divisibility-gamma: that asks whether Winter's tracial divisibility of every positive element forces uniform Gamma; this assumes divisibility of the unit only and concludes bounded rank density, not Gamma.
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
---

Let `A` be a unital separable C*-algebra whose trace simplex `T(A)` is a nonempty
Bauer simplex. Say the unit of `A` is **tracially `N`-divisible** if for every
`ε > 0` there is a c.p.c. order zero map `φ: M_N → A` with `τ(φ(1)) > 1 − ε` for
every `τ ∈ T(A)`. Equivalently, the uniform tracial ultrapower `A^U` contains a
unital copy of `M_N`.

**Theorem.** If the unit of `A` is tracially `N`-divisible for arbitrarily large
`N`, then `A` has bounded rank density (RD_b). That is, for every `k`, every
continuous affine `f: T(A) → [0,k]` and every `η > 0`, there is a positive
contraction `b ∈ M_k(A)` with `sup_τ |τ(b) − f(τ)| < η` and `sup_τ τ(b − b²) < η`.

No comparison, nuclearity, simplicity or dimension hypothesis is used.

**Proof idea.**
- **Divide the unit.** The elements `e_j = φ(e_jj)` are orthogonal, and every
  trace gives `τ(e_j) = τ(φ(1))/N` and `τ(e_j − e_j²) = τ(φ(1) − φ(1)²)/N`.
- **Central functions.** Ozawa's Theorem 3 (arXiv:1304.3523) embeds
  `C(∂_e T(A))` centrally in the strict closure of `A`, with
  `λ(θ(ψ)a) = ψ(λ)λ(a)` at extreme traces `λ`.
- **Step functions.** Take a fine partition of unity `φ_i`, put
  `r_i = ⌊N f(λ_i)⌋` and `ψ_j = Σ_{r_i ≥ j} φ_i`. Then `B = Σ_j θ(ψ_j) e_j` has
  profile within `η/2` of `f` and defect below `η/3`. Its pieces commute exactly,
  and at each point only `O(Nη)` of the `ψ_j` lie strictly between 0 and 1.
- **Pull back.** Norm-bounded 2-norm approximants of the central `θ(ψ_j)` move `B`
  into `A`.

Full proof: Section 1 of the artifact.

**Consequence.** Under strict comparison the converse also holds, since a
projection of constant trace `1/N` divides the unit by projection comparison. So
on Bauer simplices, bounded rank density is exactly tracial divisibility of the
unit (`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`).
