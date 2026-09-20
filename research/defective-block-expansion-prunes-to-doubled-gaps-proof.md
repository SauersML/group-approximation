---
rg: 2
id: defective-block-expansion-prunes-to-doubled-gaps-proof
kind: route
title: "Liu's pruning and two-unitary dilation remove summable expansion defects"
target: defective-block-expansion-prunes-to-doubled-gaps
requires: []
artifacts:
  - research/artifacts/liu-analytic-leaves-proof-acceptance-2026-09-20.md
---

## Attribution and proof

This is an independently verified exposition of **Jihao Liu**,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Lemma 5.4, not a new result or mechanism of Cairn.
Section D of the acceptance artifact is the full proof.

Discard a block only when xi_i>theta tr(P_i)/8. Otherwise repeatedly
remove half-size subprojections whose compressed energy is below
kappa times trace, with kappa=theta/8. The boundary of every initial
removed segment is bounded by the sum of its removal energies. A first
crossing of tr(P_i)/4 would have trace below 5tr(P_i)/8; applying the
original expansion estimate to the smaller side contradicts that
boundary bound. Thus pruning loses at most 8xi_i/(7theta) on retained
blocks and leaves original-generator boundary energy at most xi_i/7.

The terminal compressed contractions have half-rank projection
expansion kappa. Layer-cake applied to y^2 and row/column contraction
bounds prove the Cheeger inequality Q(y)>=kappa^2 tr(y^2) on positive
half-support matrices. A median decomposition proves it for selfadjoint
trace-zero matrices; the adjoint-preserving quadratic-form operator
then proves it for every complex trace-zero matrix.

For each compressed contraction a=v|a|, the two unitaries
v(|a| +/- i sqrt(I-|a|^2)) average to a. Applying convexity also to
a* gives scalar gap kappa^2=theta^2/64 for the doubled list with its
correct denominator 8h. Orthogonality of the final matrix blocks gives
```
sum_(j,+/-)||z_j^+/- - w_j||_2^2
  =8h sum_R E_w(R)
  =16h sum_(i>=1)E_w(R_i) <=16h xi/7.
```
The lost-trace estimate, summable boundary estimate, and doubled scalar
gap are precisely the target's three conclusions, with no lower bound
on individual block ranks or traces.

The artifact verifies the crossing argument, the complex-matrix
extension, the normalization after doubling, and the edit-cost identity.
This route is a full written proof, not merely acceptance based on no
gap being noticed, and is not a Lean certification.
