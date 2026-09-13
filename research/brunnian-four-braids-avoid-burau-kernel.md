---
rg: 2
id: brunnian-four-braids-avoid-burau-kernel
kind: claim
title: "No nontrivial Brunnian 4-braid lies in the kernel of the 4-strand Burau representation"
distinct_from:
  four-strand-burau-representation-is-faithful: that claim is injectivity of Burau on all of B_4; this claim is injectivity on the free normal subgroup Brun_4, which is equivalent to it only through Long's theorem
---

For every `1 ≠ Φ ∈ Brun_4`, `ρ_4(Φ) ≠ I`. This is Theorem 6.6 of arXiv:2607.05283v1
(Bharathram–Birman–Brendle, unrefereed).

## Attempts

- 2026-09-13 (lane z3-05-burau-theory): the preprint's chain for this theorem is:
  - B1: nontrivial Brunnian 4-braids are pseudo-Anosov. Independently proved:
    `brunnian-four-braids-are-pseudo-anosov`.
  - B2: conjugate `Φ` to a proper product with `ι(α, (β_*^3)Φ) > 0` (Lemma 6.3).
  - B3: for `f : B_4 → B_5`, some push map `Γ ∈ K_5` makes `f(Φ)·Γ` and `Γ` both satisfy parity,
    with different intersection counts (Proposition 6.4, Corollary 6.5). Recorded as
    `brunnian-four-braids-have-five-strand-moody-witness`.
  - B4: no cancellation (Lemma 4.2); the logic is checked.
  - B5: Moody's criterion, `moody-polynomial-change-certifies-burau-nonkernel`.
  - B6: `f(Φ) ∉ ker ρ_5 ⇒ Φ ∉ ker ρ_4`. Independently proved:
    `burau-kernel-restricts-along-strand-inclusion`.
- 2026-09-13 (check owner z3-05-burau-search, artifacts
  `zp-burau-n4-verification-2026-09-13-part1.md` and `-part2.md`, landed 5c5c59481a):
  - **Checked OK:** the reduction to `Brun_4`, Moody's criterion, Lemma 4.2, the `n = 3` proof,
    and the Section 7 bookkeeping.
  - **GAP in the core:**
    - G1 (decisive): the loop-insertion step at the end of Proposition 6.4 asserts an increase of
      `ι` and preserved parity without proof. That step carries the whole theorem.
    - G2: parity of `Γ` in the first stage (the five disk types, staged pushes along non-closed
      paths).
    - G3: routing of `γ_2`.
    - G4: proper product of `f(Φ)·Γ`, and Proposition 5.1 applied outside `K_5`.
    - G5: free reduction ⇒ Condition 2 in Theorem 6.6.
    - G6: pseudo-Anosov ⇒ `ι > 0`. REPAIRED up to powers by
      `brunnian-four-braid-powers-cross-the-base-arc` (established).
    - Lemmas 6.2–6.3 rest on figures only.
  - Details in `brunnian-four-braids-have-five-strand-moody-witness`.
- No-side evidence (check owner, unreviewed): a meet-in-the-middle search found no Burau kernel
  element in `K_4` of free length ≤ 20 in the basis `A14, A24, A34`. A positive control and a
  length-24 run are under way.
- Status: OPEN. The architecture (B1, B4, B5, B6, and G6 through powers) is sound. The theorem
  rests on repairing G1–G5 or on a different proof of the witness claim.
