---
rg: 2
id: fpbs-mal-single-generator-packing-floor-uniform-proof
kind: route
title: Rigidity of stage generators plus the double-coset packing floor
target: fpbs-mal-single-generator-packing-floor-uniform
requires:
  - fpbs-mal-stage-generators-lie-in-b-double-coset
  - fpbs-malnormal-coset-cycles-linear-perimeter
artifacts:
  - research/artifacts/fpbs-mal-stage-generator-rigidity-2026-09-17.md
---

Let `<H_n, t> = H_m`.
1. By [[fpbs-mal-stage-generators-lie-in-b-double-coset]],
   `t ∈ H_n b_m^{±1} H_n`.
2. By Item 4 of [[fpbs-malnormal-coset-cycles-linear-perimeter]], every packing
   certificate for `relC(H_m; H_n)` with a generator in `H_n b_m^{±1} H_n` is
   at least `δ_mal`. See §6 of that node's artifact: substituting
   `t = h b_m^ε h'` injectively turns `t`-detours into `b_m`-detours with the
   same number of new letters.

So every single-generator certificate is at least `δ_mal`, uniformly over
`n < m` and `t`. Hence `inf_j exp(-h_{t_j}) >= δ_mal > 0`, which contradicts
[[fpbs-mal-long-generator-packing-growth]]. Details are in §5 of the artifact.
