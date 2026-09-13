---
rg: 2
id: brunnian-four-braids-have-five-strand-moody-witness
kind: claim
title: "Every nontrivial Brunnian 4-braid has, up to conjugacy, a five-strand push map changing its Moody polynomial"
distinct_from:
  moody-polynomial-change-certifies-burau-nonkernel: that claim is the general criterion turning a change of Moody polynomial into non-membership in the Burau kernel; this claim is the existence of such a change for Brunnian 4-braids
---

For every `1 ≠ Φ ∈ Brun_4` there is a conjugate `Φ_0` of `Φ` in `B_4` and a push map
`Γ ∈ K_5 = π_1(D_4, p_5) ⊂ B_5` with `𝕄_{f(Φ_0)·Γ} ≠ 𝕄_Γ`. Here `f : B_4 → B_5` is the inclusion
adding `p_5`, and `𝕄` is as in `moody-polynomial-change-certifies-burau-nonkernel` with `n = 5`.

This combines Lemma 6.3, Proposition 6.4 and Corollary 6.5 of arXiv:2607.05283v1
(Bharathram–Birman–Brendle).

## Attempts

- 2026-09-13 (lane z3-05-burau-theory): the preprint's mechanism is:
  - conjugate `Φ` to a proper product with `ι(α, (β_*^3)Φ) > 0`, which needs `Φ` pseudo-Anosov
    (established: `brunnian-four-braids-are-pseudo-anosov`);
  - construct `Γ` so that `f(Φ)·Γ` is a proper product, both braids satisfy the parity condition
    (a disk between consecutive intersections changes sign iff it holds an odd number of
    punctures), and the intersection numbers differ;
  - no cancellation (Lemma 4.2) plus minimal position (Proposition 5.1) then turn "intersection
    numbers differ" into "Moody polynomials differ".

  The logic of the last step is checked in artifact §2.7. The construction of `Γ` and the parity
  verification are NOT checked here. The HTML extraction flags two places for the line-by-line
  check: a "without loss of generality" in the second case of Proposition 6.4, and figure-based
  isotopies in Lemma 6.2. Owner of the check: lane z3-05-burau-search.
