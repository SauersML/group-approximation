---
rg: 2
id: regular-rank-ring-fixed-right-ideal-conservation-proof
kind: route
title: Intersect principal annihilators, bound the complement by modularity, and upgrade containment to equality by faithfulness
target: regular-rank-ring-compressors-conserve-fixed-right-ideals
requires: []
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
---

Artifact Section 2, Theorem 2.2. Inputs are the dimension calculus of principal right ideals in a
regular ring with a rank function (Goodearl, *Von Neumann Regular Rings*, Chapter 16, at statement level,
as in `research/artifacts/two-root-defect-descent-gap-2026-09-12.md` Fact 1.1).

1. **Principal.** `Fix_r(sigma(Gamma))` is the finite intersection of the principal right annihilators of
   `sigma(s) - 1`, hence principal, `eU`.
2. **Bound.** For `J = xU`, `rk((1-e)x) = rk(J) - rk(J cap eU)` and
   `rk((sigma(s)-1)x) = rk(J) - rk(J cap rann(sigma(s)-1))`, both from rank-nullity for principal right
   ideals. Modularity inside `J` sums the codimensions.
3. **Conservation.** For `g` in `P_Gamma`, `eU <= sigma(g) eU`, and the two have equal rank. A principal
   complement of rank `0` vanishes by faithfulness, so `sigma(g) eU = eU`.
4. **Normal closure.** Conjugates of elements of `Gamma` fix `eU` pointwise, because `sigma(G)` preserves
   `eU`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 18.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
