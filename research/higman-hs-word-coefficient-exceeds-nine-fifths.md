---
rg: 2
id: higman-hs-word-coefficient-exceeds-nine-fifths
kind: claim
title: A two-dimensional rational Higman tuple forces its HS word coefficient above nine fifths
distinct_from:
  higman-hs-microstates-are-near-glued-exact-bs-cycles: that equates vanishing-defect sequences with four nearly matching exact BS packets; this gives a finite exact lower bound on one proposed global energy coefficient and no vanishing-defect sequence.
  failed-hs-word-bounds-have-rational-witnesses: that guarantees a rational witness when a coefficient fails; this gives explicit matrices refuting every coefficient below one particular rational value for the Higman four-cycle.
artifacts:
  - research/artifacts/higman-hs-word-coefficient-lower-bound.md
  - research/artifacts/higman-hs-word-coefficient-witness.json
  - experiments/hs_word_certificate.py
---

For the Higman relators r_j=g_j g_(j+1) g_j^(-1) g_(j+1)^(-2), cyclically
indexed, any coefficient C in the all-dimensions inequality

```
||U_0-I||_2^2 <= C sum_(j=0)^3 ||r_j(U)-I||_2^2
```

must satisfy `C >= 2748800041/1512087866 > 9/5`. This follows already
in dimension two from the explicit rational matrices in the artifact.
No upper bound, dimension-uniform gap, nontrivial radical word, or
hyperlinearity conclusion is established.
