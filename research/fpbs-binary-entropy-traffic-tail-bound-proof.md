---
rg: 2
id: fpbs-binary-entropy-traffic-tail-bound-proof
kind: route
title: Predict reuse bits, split repeated-traffic tails, and count periodic connector routes
target: fpbs-binary-entropy-traffic-tail-bound
requires:
  - fpbs-conditional-traffic-descent-bound
artifacts:
  - research/artifacts/fpbs/docs/binary-descent-entropy-tail.md
  - research/artifacts/fpbs/binary-descent-entropy-tail-verifier.py
---

Section 1 bounds the scalar conditional clipping defect by T times the Bayes
error for its reuse flag plus the repeated-traffic tail. Binary entropy is at
least 2 log 2 times that Bayes error. Integrate over the base and sum over all
edge copies. The prerequisite supplies the resulting actual base cost bound;
a fixed cutoff followed by the entropy limit proves the uniform-integrability
criterion. Its countable-group scope requires a finite-cost base and includes
the complete unprocessed base graphing tail in the source budget.

Sections 2--3 give the explicit countermodel on a single odometer extension.
The two edge labels are +1 and +2. Formula (4) counts all routed requests,
including the last odd request crossing to the next period. Those counts give
B=1, J=1 and H=h(1/q)+h(2/q)->0. The full generator graphing and the aperiodic
cost lower bound give cost one for both actions. The verifier checks finite
traffic tables; the written formulas establish the all-period assertion.
