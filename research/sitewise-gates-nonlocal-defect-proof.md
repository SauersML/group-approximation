---
rg: 2
id: sitewise-gates-nonlocal-defect-proof
kind: route
title: A nonlocal remainder is transcendental over the local variables, so a local output forces the gate to ignore the copy
target: sitewise-gates-cannot-erase-nonlocal-defects
requires: []
artifacts:
  - research/artifacts/stable-formalization-erasure-audit-2026-09-12.md
---

Section 3 of the artifact.
- **Lemma.** A polynomial `d ∈ k[S][T] \ k[S]` is transcendental over `k(S)`. If `P(d) = 0` with
  `P ∈ k(S)[w]` of degree `r >= 1`, the `T`-degree of `P(d)` is `r · deg_T(d) > 0`, a contradiction.
- **Proof of the claim.** `P(w) = F(w) − F(c + d)` lies in `k(S)[w]` and has the transcendental root
  `c + d`. So `P = 0`, and `F` is independent of `w`.
