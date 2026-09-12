---
rg: 2
id: relative-rigid-defect-from-kazhdan-quotient-permanence
kind: route
title: Apply the absolute sofic defect criterion to the quotient by the Kazhdan kernel
target: sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels
requires:
  - sofic-quotients-by-kazhdan-normal-subgroups-are-sofic
  - sofic-groups-kill-rigid-compression-defects
artifacts:
  - research/artifacts/hyperbolic-leavitt-cover-relative-defect-2026-09-12.md
---

Let `H` be sofic, `M` normal Kazhdan, and `Gamma <= G <= H` a rigid pair with
`M <= Gamma`.

1. By the first premise, `H/M` is sofic.
2. `Gamma/M <= G/M` is a rigid pair in `H/M`: quotients of Kazhdan groups are
   Kazhdan, and images of compressors compress.
3. For `z` with `[z, Gamma] <= M`, the coset `z M` centralizes `Gamma/M`.
4. The absolute criterion in `H/M` gives `[g z g^-1, gamma] M = M`. ∎
