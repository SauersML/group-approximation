---
rg: 2
id: el-2-minimal-subshift-kazhdan-via-idempotent-grading
kind: route
title: Answer the rank-two question positively through complementary full idempotents e_W, 1−e_W and an A_2 grading
target: el-2-over-every-minimal-subshift-algebra-is-kazhdan
requires:
  - subshift-el-2-is-simple-kazhdan-lef
---

The open claim asks two things about every infinite minimal subshift `X`, Sturmian included:
- whether `EL_2(LC(X,F_2) ⋊ Z)` has property (T);
- whether it is simple.

`subshift-el-2-is-simple-kazhdan-lef` gives both, plus LEF.
- **The Morita obstruction is avoided.** Attempt 1 of the open claim showed that `M_2(R) ≅ M_k(S)` with `k ≥ 3` fails for Sturmian `X`.
  The grading of `complementary-full-idempotents-make-el-2-kazhdan` needs no matrix-ring structure, only one idempotent `e_W` with
  `e_W` and `1−e_W` full.
- **Attempt 2's gap.** Relative (T) for non-isomorphic corners is not needed.
  - The same `e_W` is used in both coordinates, so the two blocks `e_W R ⊕ 0` and `0 ⊕ e_W R` are isomorphic and give `EL_2(e_W R e_W)`.
  - The third block `(1−e_W)I_2` is reached through the opposite ring and bounded products.
