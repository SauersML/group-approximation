---
rg: 2
id: no-fixed-trace-precision-proof
kind: route
title: Complement the averaging idempotent on a cyclic group of order one more than a prime power
target: no-fixed-trace-precision-detects-all-idempotents
requires:
  - finite-precision-lifted-trace-obstruction
artifacts:
  - research/artifacts/kaplansky-finite-precision-trace-2026-09-07.md
---

Write N=sum_(g in C_m) [g] with m=p^r+1. Since N^2=mN, the element
E=1-N/m is an idempotent over Z_p[C_m] and reduces to the stated nonzero
e. Its identity coefficient is (m-1)/m=p^r/(p^r+1), of valuation exactly r.
Lift independence identifies its residues with t_(p,k). Section 4 of the
artifact proves the sharpness and explains why this supplies no inverse
defect or Kaplansky counterexample.
