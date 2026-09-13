---
rg: 2
id: loop-braid-cloning-system-is-properly-graded
kind: claim
title: "The Witzel–Zaremsky cloning systems on loop braid groups LB_* and PLB_* are properly graded"
artifacts:
  - research/artifacts/zp-loop-braid-cloning-properly-graded-2026-09-13.md
---

Witzel–Zaremsky, arXiv:1405.5491v3, Definition 2.16, verbatim: the cloning maps
are properly graded if "if g ∈ G_{n+1} can be written as (h)κ^n_k = g =
(ḡ)ι_{n,n+1} then there is an h̄ ∈ G_{n−1} with (h̄)κ^{n−1}_k = ḡ and
(h̄)ι_{n−1,n} = h" (with κ^{n−1}_n := ι_{n−1,n}).

Claim: the cloning systems of their Lemma 10.1 on `LB_* = ΣAut_*` and on
`PLB_* = PΣAut_*` satisfy this.

The proof is in the artifact and is summarized in the route
`loop-braid-cloning-system-is-properly-graded-proof` (unreviewed). Its key
input is Lemma A: cloning commutes with merging,
`L((g)κ_k) ∘ δ_k = δ_{ρ(g)k} ∘ L(g)`, where `δ_k(x_k) = x_k x_{k+1}` and
`L(g) = (x ↦ x^{g^{-1}})` converts WZ's right-action products to composition.
