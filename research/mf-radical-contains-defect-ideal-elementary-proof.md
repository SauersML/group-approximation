---
rg: 2
id: mf-radical-contains-defect-ideal-elementary-proof
kind: route
title: Normal closure of the torsion defects, summed over all one-sided pairs
target: mf-radical-contains-defect-ideal-elementary-subgroup
requires: [finite-additive-order-one-sided-defects-are-mf-invisible]
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

For each one-sided pair with defect `e`, the required claim puts `e_ij(e)` in `Rad_MF(EL_n(R))` for all
`i != j`. The radical is normal, so it contains `[e_ki(a), e_ij(e)] = e_kj(ae)` and
`[e_kj(ae), e_jl(b)] = e_kl(aeb)` for distinct indices, and signed permutations move the index pair.
An element of `d(R)` is a finite sum of terms `a e b` over finitely many pairs, and
`e_ij(x + y) = e_ij(x) e_ij(y)`, so every generator `e_ij(x)`, `x in d(R)`, of `EL_n(R, d(R))` lies in
the radical, and so does their normal closure.
