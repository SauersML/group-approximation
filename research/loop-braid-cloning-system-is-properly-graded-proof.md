---
rg: 2
id: loop-braid-cloning-system-is-properly-graded-proof
kind: route
title: "Proper grading of the loop braid cloning systems via cloning-merging intertwining and free-factor intersections"
target: loop-braid-cloning-system-is-properly-graded
requires: []
artifacts:
  - research/artifacts/zp-loop-braid-cloning-properly-graded-2026-09-13.md
---

Complete hand proof (unreviewed), written out in the artifact.

1. **Conventions.** WZ's products in `LB_n = ΣAut_n` are right actions: the
   FRR97 relation `β_iβ_{i+1}σ_i = σ_{i+1}β_iβ_{i+1}` holds only in that
   reading. `L(g) := (x ↦ x^{g^{-1}})` is an isomorphism onto composition, and
   `L(g)(x_i)` is a conjugate of `x_{ρ(g)(i)}`.
2. **Lemma A.** `L((g)κ_k) ∘ δ_k = δ_{ρ(g)k} ∘ L(g)`, where
   `δ_k: x_k ↦ x_k x_{k+1}` shifts the higher indices. It is checked on
   `β_i, σ_i` for all four positions of k using formulas (10.1)–(10.2), and
   extended to all g by (FCS1).
3. **Proper grading.** If `(h)κ_k = ι(ḡ)`, then `ψ = L((h)κ_k)` fixes
   `x_{n+1}` and preserves `F_n`.
   - For `k < n`: abelianization plus the centralizer of `x_{n+1}` force
     `L(h)(x_n) = x_n`. Intersecting the free factors `⟨x_1, …, x_n⟩` and
     `δ_j(F_n)` inside the basis `{…, x_j x_{j+1}, x_{j+1}, …}` forces
     `L(h)(F_{n−1}) ⊆ F_{n−1}`.
   - For `k = n`: abelianization gives `ρ(h)(n) = n`. A reduced-word argument
     in the free factor `⟨x_1, …, x_{n−1}, x_n x_{n+1}⟩` forces the conjugator
     of `x_n` to be a power of `x_n x_{n+1}`, hence `L(h)(x_n) = x_n` and
     `L(h)(F_{n−1}) ⊆ F_{n−1}`.
   - In both cases `h = ι(h̄)` with `h̄ ∈ LB_{n−1}` (pure when h is), and
     (2.5) plus the injectivity of ι give `ḡ = (h̄)κ^{n−1}_k`.
