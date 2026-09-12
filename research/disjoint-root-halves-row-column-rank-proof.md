---
rg: 2
id: disjoint-root-halves-row-column-rank-proof
kind: route
title: The kernel of the sum of two halves maps onto their range overlap with kernel the joint annihilator, and the joint annihilator is the annihilator of the left ideal
target: disjoint-root-halves-row-plus-column-rank-at-most-three-rho
requires:
  - near-minimal-defect-ranges-are-rank-faithful-for-the-commutant
artifacts:
  - research/artifacts/halving-expansion-and-commutant-faithfulness-2026-09-12.md
---

Artifact Section 4.

1. **Subproducts.** `prod_(i in S) tau(C_i <- C'_i) = 1 + sum_(i in S) S[C_i]T[C'_i]`. A prefix replacement
   sends `C_i -> D w_i` and `C'_i -> D' w_i` for a complete prefix code `(w_i)`, and the complement to the
   complement. So the product is conjugate to `tau(D <- D')`.
2. **Kernels of sums.** `a + b + ab = (1+a)(a+b)` for commuting square-zero `a, b`, so
   `rk(sigma(tau tau') - 1) = rk(a + b) = rho`.
3. **Row plus column.**
   * `K = r.ann(a+b)` has rank `1 - rho`.
   * `x -> ax` on `K` has kernel `r.ann(a) ∩ r.ann(b) = r.ann(Ma + Mb)`, of rank `1 - rk(Ma + Mb)`.
   * Its image lies in `aM ∩ bM`, of rank `2 rho - rk(aM + bM)`.
   * Adding gives `1 - rho <= 1 - rk(Ma+Mb) + 2rho - rk(aM+bM)`.
4. **Independent halves.** Insert the two lower bounds: `4rho - 2rho^2 - 2eta <= 3rho`.
5. **Near-minimal displacement.**
   * **Faithfulness.** Run the proof of `near-minimal-defect-ranges-are-rank-faithful-for-the-commutant`
     with `rho_*` in place of `c_*`: corner models of clopen cylinder groups have displacement at least
     `rho_*`.
   * **Overlap.** With `K = r.ann(b)` invariant under the cylinder group of `a`, `rk(aK) >= rho_*(1 - rho)`,
     so `rk(Ma + Mb) >= 2rho - rho^2 - eps rho`. Item 3 then gives the range overlap.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 19.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
