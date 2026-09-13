---
rg: 2
id: leavitt-3-4-module-iso-image-normally-generates-e3
kind: claim
title: For R = L_K(3,4) and an isomorphism R^4 ≅ R^3, the conjugate of EL_4(R) lies in EL_3(R) and normally generates it
---

Let `K` be a field, `R = L_K(3,4)`, and `X ∈ M_{3×4}(R)`, `Y ∈ M_{4×3}(R)` with `XY = 1_3` and `YX = 1_4`. Put
`Φ(g) = XgY`, a group isomorphism `GL_4(R) → GL_3(R)`. The claim has two parts:

1. `Φ(EL_4(R)) ⊆ EL_3(R)`, i.e. `1 + x_i r y_j ∈ EL_3(R)` for all `i ≠ j` in `{1,…,4}` and all `r ∈ R`, where `x_i`
   are the columns of `X` and `y_j` the rows of `Y`;
2. the normal closure of `Φ(EL_4(R))` in `EL_3(R)` is `EL_3(R)`.

Changing `X` to `EXF` with `E ∈ GL_3(R)` and `F ∈ GL_4(R)` does not change the truth of the claim.

## Attempts
- **Suslin conjugation: dead.** It would write `x_i = g e_1` with `g ∈ EL_3(R)`, and then
  `1 + x_i r y_j = g(1 + e_1 r y_j g)g^{-1}` with `1 + e_1 r y_j g ∈ ⟨e_12, e_13⟩`. By
  `leavitt-module-rank-iso-columns-are-not-completable`, no column of any such `X` is even `GL_3`-completable.
- **Free coordinate: dead.** There is none, by the same claim. The mechanism of
  `non-ibn-ring-el-n-full-mf-radical-above-module-rank` needs one.
- **Normal-closure isolation: dead in its standard form.** Conjugating a transvection `1 + v r w` to an elementary
  matrix again needs `v ∈ EL_3·e_1`.
- **What is left.** Part 1 is a Suslin-normality statement for non-completable unimodular columns over a
  noncommutative ring that is not module-finite over its centre. Normality of `E_n` fails over some noncommutative
  rings (Gerasimov, recalled, not re-read). Any proof must use the Leavitt relations `Σ_i x_i y_i = 1_3` and
  `y_j x_i = δ_ij` directly. Stably the transvections are elementary (`K_1` is Morita invariant), so there is no `K_1`
  obstruction, but unstable membership is open.
- **Symmetry.** The inverse conjugation `h ↦ YhX` sends `e_kl(r)` to `1_4 + y'_k r x'_l`, where `y'_k` is a column
  of `Y` and `x'_l` a row of `X`. Its columns are non-completable in `GL_4` too, so the reverse inclusion
  `Φ^{-1}(EL_3) ⊆ EL_4` is equally out of reach of the standard tools.

Details: `research/artifacts/un-low-rank-band-noncompletable-columns-2026-09-13.md` §3.
