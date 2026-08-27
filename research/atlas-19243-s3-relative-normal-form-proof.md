---
rg: 2
id: atlas-19243-s3-relative-normal-form-proof
kind: route
title: Read collision 19243 through the fixed alignment and realize it in amplified Reg(S4)
target: atlas-19243-s3-relative-normal-form
requires: []
artifacts:
  - experiments/atlas-word-19243.json
  - experiments/atlas_19243_s3_relative.py
---

The replay script performs the finite arithmetic used in the claim.

1. It conjugates the four stored second-chart `GL_4(F_2)` matrices by the
   certified classical alignment and checks that they are exactly
   `r,s,r^2,sr`, with `r^3=s^2=1` and `srs=r^-1`.
2. It checks that the repeated first-chart syllable is an involution.
3. In `S_4` it verifies directly that

   ```text
   r=(1 2 3), s=(1 2), c=(1 3)(2 4)
   ```

   satisfies `r c s c r^-1 c (s r) c=1`, and that these three elements
   generate a group of order `24` while `<r,s>` has order `6`.
4. The regular-restriction multiplicities are pure coset counting:
   `20160/6=3360` and `840*(24/6)=3360`.  Hence the two `S_3`
   representations are unitarily equivalent.
5. A nonidentity involution in a regular representation has trace zero.  Thus
   both the transported `S_4` involution and the fixed regular `A_8`
   involution have `10080` eigenvalues of each sign, so they are unitarily
   conjugate.  Choosing that conjugator as the relative chart unitary realizes
   the original word at defect zero.

All steps are finite exact group/matrix arithmetic; no limiting or numerical
argument is used.
