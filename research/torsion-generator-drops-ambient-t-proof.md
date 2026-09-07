---
rg: 2
id: torsion-generator-drops-ambient-t-proof
kind: route
title: Transport kills the defect in Hilbert-Schmidt norm, and the shadow equivalence closes it
target: torsion-normal-generator-drops-ambient-property-t
requires:
  - kazhdan-asymptotic-commutant-transport
  - op-to-hs-shadow-residual-functoriality
  - torsion-normal-generator-mf-shadow-equivalence
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

## Why sufficient

Write `S(G) = R_(infinity->2)(G)` for the shadow residual.

**The defect lies in the shadow residual.**  Let `u in Comp_G(L)`,
`c in C_G(L)`, `l in L`, and let `(V_n)` be an operator-norm asymptotic
representation of `G`.  Conjugation by `V_n(u)` preserves the Hilbert--Schmidt
asymptotic commutant of `L` by `kazhdan-asymptotic-commutant-transport`, and
`V_n(c)` lies in that commutant, so `V_n(ucu^(-1))` does as well; then
`V_n([ucu^(-1), l])` tends to the identity in normalized Hilbert--Schmidt
norm.  These commutators generate `D_G(L)` as a normal subgroup, and
`op-to-hs-shadow-residual-functoriality` makes `S(G)` a normal subgroup, so
`D_G(L) <= S(G)`.

**Closing.**  By hypothesis `a in D_G(L) <= S(G)`.  By
`torsion-normal-generator-mf-shadow-equivalence`, applied to the finite-order
normal generator `a`, membership in `S(G)` is equivalent to membership in
`Rad_MF(G)`, so `a in Rad_MF(G)`.  The MF radical is normal, and `a`
normally generates `G`, so `Rad_MF(G) = G`.
