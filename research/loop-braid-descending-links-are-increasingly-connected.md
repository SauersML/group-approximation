---
rg: 2
id: loop-braid-descending-links-are-increasingly-connected
kind: claim
title: "The descending links L_n(LB_*) of the loop braid cloning system become arbitrarily highly connected"
---

For the cloning system on `LB_n = ΣAut_n` (Witzel–Zaremsky, arXiv:1405.5491v3,
Lemma 10.1), and for every m ≥ 0, there is N such that the simplicial complex
`L_n(LB_*)` is m-connected for all n ≥ N.

Definition (their §5.3, p. 31): a simplex of `L_n(G_*)` is a class `[g, Γ]`,
with `g ∈ G_n` and Γ a non-trivial matching of the linear graph `L_n`. Two
pairs `(g_1, Γ_1)`, `(g_2, Γ_2)` are equivalent if Γ_1 and Γ_2 have the same
number m of edges, `g_2^{-1} g_1 ∈ im κ_{Γ_1}`, and
`Γ_2 = (g_2^{-1} g_1)κ_{Γ_1}^{-1} · Γ_1`. Faces come from subgraphs. By their
Observation 5.8 this is the descending link in the Stein–Farley complex.

## Attempts

- 2026-09-13 (lane z2-12-loop-bv), complete join over the combinatorial
  matching complex: DEAD for the pure system.
  - Take `e: PΣAut_n → Z^{n(n−1)}`, where `e_{ij}(φ)` is the exponent sum of
    `x_j` in a conjugator `w_i` with `φ(x_i) = w_i x_i w_i^{-1}`.
    - It is well defined because the centralizer of `x_i` is `⟨x_i⟩`.
    - It is a homomorphism because pure symmetric automorphisms preserve
      exponent sums.
  - Let `H_k = im κ_k`. Every element of `H_1` has `e_{13} = e_{23}` and
    `e_{14} = e_{24}`; every element of `H_3` has `e_{13} = e_{14}` and
    `e_{23} = e_{24}`.
  - So `f = e_{13} − e_{23} − e_{14} + e_{24}` vanishes on `H_1 H_3`, but
    `f(α_{13}) = 1` for `α_{13}: x_1 ↦ x_3 x_1 x_3^{-1}`. Hence
    `PΣAut_n ≠ H_1 H_3`.
  - So two merge vertices over the disjoint edges `e_1, e_3` do not always
    span a simplex, and `L_n(PLB_*) → M(L_n)` is not a complete join.
  - Geometric reason: the two cabling tubes can link.
- 2026-09-13, repair idea (open): take as base the complex of disjoint
  2-spheres in the complement of the n unlinked loops, each bounding a ball
  that contains exactly two loops.
  - A split sphere guarantees that a merge inside its ball is independent of
    merges in the other balls.
  - The expected structure is a complete join over this sphere complex.
    Connectivity of the sphere complex would then come from Hatcher–Wahl-type
    surgery on sphere systems (compare Aramayona–Bux–Flechsig–Petrosyan–Wu,
    arXiv:2110.05318, Section 8).
