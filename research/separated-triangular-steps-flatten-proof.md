---
rg: 2
id: separated-triangular-steps-flatten-proof
kind: route
title: Multiply the padded triangular matrix by block-separated minors, then clear the unitriangular corner
target: separated-triangular-steps-flatten-to-minors
requires: []
artifacts:
  - research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md
---

Section 1 of the artifact.
1. **Minors in block form.** Write `f = L_A A R_A + L_1 Z_1 R_1` and `g = L_B B R_B + L_2 Z_2 R_2`.
2. **Padded matrix.** Order the rows and columns of `W = T (+) Z_1 (+) Z_2` as (`A`, `B`, `Z_1`, `Z_2`), so
   `W = [[A, C, 0, 0], [0, B, 0, 0], [0, 0, Z_1, 0], [0, 0, 0, Z_2]]`.
3. **Multiply.** With `𝓛 = [[L_A, 0, L_1, 0], [0, L_B, 0, L_2]]` and
   `𝓡 = [[R_A, 0], [0, R_B], [R_1, 0], [0, R_2]]`, the product is `𝓛 W 𝓡 = [[f, D], [0, g]]`, where
   `D = L_A C R_B`. The lower-left block is zero because the rows of `B` and `Z_2` vanish under the
   columns of `A` and `Z_1`.
4. **Compress and clear.** Compressing by `diag(f, g)` gives `[[f, fDg], [0, g]]`, and right multiplication
   by `[[f, -fDg], [0, g]]` gives `f (+) g`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 37.1 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the rows of `W𝓡`, and the vanishing lower-left block of `𝓛W𝓡`;*
- *the compression `[[f, fDg], [0, g]]`, and the clearing product.*

*Spot-check by `w6-vf-chain` (2026-09-12), Section 1.5 of `research/artifacts/gk-vf-chain-verification-2026-09-12.md`: PASS. Re-derived the block product, the compression by `diag(f, g)` and the clearing.*
