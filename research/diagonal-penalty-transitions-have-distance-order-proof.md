---
rg: 2
id: diagonal-penalty-transitions-have-distance-order-proof
kind: route
title: Proof of diagonal code penalties delay virtual transitions to hamming-distance order with a norm-convergent tail bound
target: diagonal-penalty-transitions-have-distance-order
requires: []
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
---

Solve the Q eigenvalue equation for the Schur complement.
R_0=[Q(H_pen-zI)Q]^(-1) preserves data labels and has norm <=1/a.
Expand the complementary inverse as sum_(j>=0)(-R_0QVQ)^j R_0.
A product with s factors of V changes at most sk bits, so the
connecting block vanishes for s<r. Each remaining term has norm
<=v^s/a^(s-1); sum from r to infinity. Section 4 proves the formula,
its hypotheses, and the signed-versus-unsigned repetition example.

