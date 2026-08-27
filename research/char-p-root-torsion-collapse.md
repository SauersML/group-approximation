---
rg: 2
id: char-p-root-torsion-collapse
kind: claim
title: Root-subgroup torsion collapses the compression in every finite-dimensional representation, modulo relative K1
distinct_from:
  ccr-for-coordinate-collapsing-models: that ASSUMES the image collapse π_n(Γ) ⊆ π_n(Λ) and proves (CCR) from it; this shows the collapse is nearly AUTOMATIC for the KT group — forced by characteristic-p torsion in every finite-dimensional unitary representation, up to one named algebraic obstruction — so the theorem's hypothesis is not a choice of chain but a structural fact.
  compressor-coset-two-point-exact: that computes the collapse in the standard congruence chain; this derives congruence-type factorization for ARBITRARY finite-dimensional representations, with no chain chosen in advance.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**Theorem (proved, with the modulo clause).**  Let
`G = EL_r(R) ⋊ SL_d(ℤ)`, `R = 𝔽_q[x₁^{±1}…x_d^{±1}]`, `r ≥ 3`, char
`p`.  For EVERY finite-dimensional unitary representation
`ρ : G → U(n)`:

1. Each root subgroup `U_ij = e_ij(R) ≅ (R,+)` is an infinite
   elementary abelian `p`-group, so `ρ(U_ij)` is a simultaneously
   diagonalizable `p`-torsion abelian subgroup of `U(n)` — hence
   FINITE (order ≤ `p^n`), and `A_ij = ker ρ|_{U_ij}` has finite
   additive index in `R`.
2. `A = ⋂ A_ij` has finite index; normality of `ker ρ` plus the
   Steinberg relation `[e_ik(a), e_kj(f)] = e_ij(af)` puts
   `e_ij(J) ⊆ ker ρ` for the ideal `J = A·R`, and `R/J` is FINITE
   (a finite-codimension subspace of `A` supplies all but finitely
   many monomials up to a fixed finite-dimensional correction).
3. So `ρ` factors, on the elementary part `E`, through
   `Ē = E/E_r(J)` — a central extension (Mennicke centrality,
   `r ≥ 3`) of a subgroup of the finite group `EL_r(R/J)` by the
   relative `K₁`-type group `K(R,J)`.  In `EL_r(R/J)` the unit trick
   (`x̄` has finite multiplicative order, so `x̄⁻¹` is a positive
   power) plus normality of the elementary part give the full
   collapse `π̄(Γ) = π̄(Λ) = π̄(E)`.  Hence

   ```text
   ρ(E) = ρ(Λ)·Z = ρ(Γ)·Z,   Z = ρ(image of K(R,J)),  Z central in ρ(E).
   ```

**Consequence for the coordinate regime.**  If the central piece acts
trivially enough — in particular whenever the relative `SK₁(R, J)`
vanishes for the finite-codimension ideals arising — then EVERY
coordinatewise ultraproduct of genuine finite-dimensional
representations of `G` satisfies the image-collapse hypothesis of
`ccr-for-coordinate-collapsing-models`, and (CCR) holds for it with
no chain hypothesis at all.  The audit's "uncharted middle ground"
(genuine chains SEPARATING `Λ` from `Γ`) is thereby pinned to a
computable question: **such chains exist only if relative `SK₁` of
`(R, J)` is nontrivial and acts nontrivially** — algebraic K-theory,
not analysis.  (Absolute `SK₁` of polynomial and Laurent extensions
of fields vanishes — Suslin; Bass–Heller–Swan — but RELATIVE `SK₁`
with excision subtleties is the honest open sub-item, flagged, not
assumed.)

**What it does NOT do.**  Nothing here touches approximate
representations: `approximate-collapse-for-kt-compressor` is
untouched, and Becker–Lubotzky still guarantees far-from-genuine
almost-representations exist.  What changes is the shape of the wall:
the genuine-coordinate regime is now (modulo the `SK₁` item) FULLY
collapsing — so any (AC) counterexample must not only avoid genuine
coordinates, it must produce approximate-commutant structure that
every genuine finite-dimensional representation of `G` provably
cannot have, for torsion reasons rooted in characteristic `p`.  The
enemy's room keeps shrinking.

Proof recorded in `char-p-root-torsion-collapse-proof`.
