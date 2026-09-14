---
rg: 2
id: subshift-elementary-el-2-simple-kazhdan-lef-proof
kind: route
title: Complementary indicator idempotents give (T) by the A_2 grading; a tower commutator plus three-block level propagation gives simplicity over F_2
target: subshift-el-2-is-simple-kazhdan-lef
requires:
  - complementary-full-idempotents-make-el-2-kazhdan
  - minimal-subshift-algebra-is-simple-lef-ring
artifacts:
  - research/artifacts/sk-el2-idempotent-grading-2026-09-13-part2.md
---

Full derivation: `research/artifacts/sk-el2-idempotent-grading-2026-09-13-part2.md` §1. Outline:

1. **(T).**
   - `R` is finitely generated (`minimal-subshift-algebra-is-simple-lef-ring` item 1).
   - For a clopen `W` with `∅ ≠ W ≠ X`, finitely many translates of `W`, and of `X∖W`, cover `X`. So `e_W` and `1−e_W` are full.
   - `complementary-full-idempotents-make-el-2-kazhdan` gives (T).
   - It is infinite (`e_12(LC)`), and finitely generated because countable Kazhdan groups are (BHV Thm 1.3.1, recalled).
2. **LEF (q = 2).** `R` embeds in a matrix ultraproduct, so finitely generated subgroups of `GL_2(R)` are LEF (the import, item 3).
3. **Simplicity (q = 2).** Let `1 ≠ g ∈ N ⊴ G = EL_2(R)`, with `w ≥ 1` bounding the exponents in `g^{±1}`, and let `V` be small as in the note.
   - *Step 1.* Some `h ∈ {e_12(e_V), e_21(e_V)}` does not commute with `g`. Otherwise `g = cI` with `c ∈ LC(X,F_2)^× = {1}`.
   - *Step 2.* `k = [g,h]` lies in the tower copy `H ≅ GL_d(F_2)`, `d = 2(2w+1) ≥ 6`. That group is simple, so `H ⊆ N` and `e_12(e_V) ∈ N`.
   - *Step 3.* Take blocks `E_1 = e_VE_11`, `E_2 = e_VE_22`, `E_3 = (1−e_V)I`, all full.
     - For distinct `A, B, C`, `J_AB = {x ∈ E_AME_B : I+x ∈ N}` satisfies `J_AB·E_BME_C ⊆ J_AC` and `E_CME_A·J_AB ⊆ J_CB`, by `[I+x, I+y] = I+xy`.
     - Starting from `e_VE_12 ∈ J_12`, every `J_AB = E_AME_B`.
     - The `Y_AB` generate `G`, so `N = G`.
