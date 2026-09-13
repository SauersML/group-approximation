---
rg: 2
id: loop-braid-cloning-system-is-properly-graded
kind: claim
title: "The Witzel–Zaremsky cloning systems on loop braid groups LB_* and PLB_* are properly graded"
---

Witzel–Zaremsky, arXiv:1405.5491v3, Definition 2.16 (verbatim): the cloning
maps are properly graded if "if g ∈ G_{n+1} can be written as (h)κ^n_k = g =
(ḡ)ι_{n,n+1} then there is an h̄ ∈ G_{n−1} with (h̄)κ^{n−1}_k = ḡ and
(h̄)ι_{n−1,n} = h" (with κ^{n−1}_n := ι_{n−1,n}).

Claim: the cloning systems of their Lemma 10.1 on `LB_* = ΣAut_*` and on
`PLB_* = PΣAut_*` satisfy this.

## Attempts

- 2026-09-13 (lane z2-12-loop-bv), hand proof in progress.
  - Read products as composition. With the merge homomorphism
    `δ_k: F_n → F_{n+1}`, `x_i ↦ x_i (i<k)`, `x_k ↦ x_k x_{k+1}`,
    `x_i ↦ x_{i+1} (i>k)`, formulas (10.1)–(10.2) satisfy
    `κ_k(g) ∘ δ_k = δ_{ρ(g)k} ∘ g` on the generators `β_i^{±1}, σ_i`. By
    (FCS1) this intertwining holds for all g.
  - Proper grading then follows from abelianization and free-factor
    intersection arguments applied to `x_{n+1}` and `⟨x_1, …, x_n⟩`.
  - Write-up to land as an artifact with a `-proof` route.
