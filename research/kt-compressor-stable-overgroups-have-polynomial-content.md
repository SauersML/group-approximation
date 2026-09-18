---
rg: 2
id: kt-compressor-stable-overgroups-have-polynomial-content
kind: claim
title: For the Theorem E pair every compressor-stable overgroup of Gamma missing the normal closure meets each root subgroup exactly in its polynomial part
distinct_from:
  kt-intermediate-coset-wreaths-are-nonsofic: that proves W_Δ nonsofic for every Γ ≤ Δ with ⟨⟨Γ⟩⟩ ⊄ Δ; this is a structure theorem for such Δ that are stable under the monomial compressors, with no approximation property involved
  theorem-c-separation-iff-infranormal-coset-wreath: that shows the hyperlinear floor Δ_hl is infranormal with compression semigroup containing P_Γ; this computes, for the Theorem E pair, what that stability forces on the root subgroups of Δ_hl
  kt-pair-hyperlinear-floor-below-normal-closure: that is the open existence question for a hyperlinear W_Δ below the normal closure; this narrows where such a Δ can live but decides nothing about hyperlinearity
artifacts:
  - experiments/kt-pair-floor-2026-09-17/lemma_a_extraction.py
  - experiments/kt-pair-floor-2026-09-17/run.log
---

**ESTABLISHED (proposed; proof in `kt-compressor-stable-overgroups-polynomial-content-proof`).**
Let `A = F_q[x_1,…,x_d] ⊂ R = F_q[x_1^(±1),…,x_d^(±1)]`, `r,d ≥ 3`,
`Γ = EL_r(A) < G = EL_r(R) ⋊ SL_d(Z)` (Kun--Thom Theorem E), `N = ⟨⟨Γ⟩⟩ = EL_r(R)`.
Write the action of `SL_d(Z)` on `R` through exponents, `x^v ↦ x^(Pv)`, and put

```text
Mon = SL_d(Z) ∩ M_d(N)   (the P with P·A ⊆ A, so Mon ⊆ P_Γ),
S(Δ) = { f ∈ R : e_12(f) ∈ Δ }   (the elementary content of Δ).
```

Let `Γ ≤ Δ ≤ G` with `P Δ P^(-1) ≤ Δ` for every `P ∈ Mon`. Then:

1. `S(Δ)` is a subring with `A ⊆ S(Δ) ⊆ R`, equal to `{f : e_ij(f) ∈ Δ}` for every
   `i ≠ j`, and `N ≤ Δ` iff `S(Δ) = R`.
2. **(Content rigidity.)** If `N ⊄ Δ`, then `S(Δ) = A`: for all `i ≠ j`,
   `e_ij(f) ∈ Δ ⇔ f ∈ A`. The key step (Lemma A) is that an `A`-submodule of `R`
   containing `A`, stable under `Mon` and different from `A`, contains every `x_j^(-1)`.
3. **(Projection dichotomy.)** `π(Δ) ⊆ SL_d(Z)` is either contained in `{±I}` or
   Zariski dense in `SL_d`. A finite `Mon`-stable subgroup of `SL_d(Z)` is central.

Two instances matter:

* `Δ = Δ_hl(Γ,G)`. `G` is residually finite, hence hyperlinear, and
  `theorem-c-separation-iff-infranormal-coset-wreath` Part 1 gives `P_Γ ⊆ P_(Δ_hl)`.
  So if `kt-pair-hyperlinear-floor-below-normal-closure` holds, the hyperlinear floor
  meets every root subgroup `U_ij(R)` exactly in `U_ij(A)`.
* `Δ' = ∩_(P∈Mon) P^(-1) Δ P` for any `Δ ⊇ Γ`. It contains `Γ`, is `Mon`-stable, and
  lies in `Δ`. If `W_Δ` is hyperlinear, so is `W_(Δ')` (see
  `kt-monomial-split-coset-wreaths-collapse-to-gamma`, step 1 of its proof).

What this does **not** give is `Δ = Γ`. A `Mon`-stable overgroup could contain
non-elementary elements of `EL_r(R)` outside `EL_r(A)`, or elements with non-monomial
projection, without enlarging its elementary content. That residual case is
`kt-compressor-stable-polynomial-content-overgroups-are-gamma`.

The experiment runs the Lemma A extraction algorithm, using only the allowed moves, on
7691 random Laurent polynomials (`d = 2..5`, `q = 5`). Every run ends at `x_j^(-1)` for
all `j`.

DERIVATION
kt-compressor-stable-overgroups-polynomial-content-proof
