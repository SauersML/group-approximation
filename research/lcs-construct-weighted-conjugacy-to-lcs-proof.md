---
rg: 2
id: lcs-construct-weighted-conjugacy-to-lcs-proof
kind: route
title: Weight Slofstra's conjugacy bundles locally and apply Culf's projection-game rounding
target: lcs-construct-weighted-conjugacy-to-lcs
requires: []
artifacts:
  - research/artifacts/lcs-constructive-compiler-2026-09-20.md
---

Sections 3--6 of the artifact are the complete proof. Four normalization
rows and three six-row conjugacy blocks give 22 rows per source conjugacy.
The standard block extensions, on two successive common doublings,
preserve exact solutions and send vanishing source defects to vanishing
target defects. Local finite abelian rounding gives perfect qa completeness.

For the reverse direction, six ordered product defects e_r bound one nice
conjugacy defect by sum_r e_r. In the normalization layer the source defect
is at most 6e_i+e_j+e_h+2c_t+c_j+c_h. Substituting the six-row bounds and
using Cauchy--Schwarz gives squared defect at most 74 times the sum of the
22 squared row-product defects.

In a tracial constraint-variable strategy, row product defect squared is
at most 4l^2 times row loss, and a pair's squared additive commutator defect
divided by four is at most eight times the sum of its two mismatch losses.
Thus each retained source linear-row energy is at most 9k^2 times row loss;
each conjugacy energy is at most 14652 times its bundle's average loss.
The inherited weights give E_source<=C_k loss_tracial with no size factor.

Eric Culf, arXiv:2603.14746v1, Corollary 7.3 converts any quantum loss
epsilon for the target constraint-variable game to finite-tracial loss
at most 148(K epsilon)^(1/4). Combining the two inequalities and solving
for epsilon gives the claimed gap. The structural gadgets and positive
model extensions retain William Slofstra's authorship (arXiv:1703.08618v2,
Lemma 4.4 and Proposition 4.2). All primary interfaces were checked.
