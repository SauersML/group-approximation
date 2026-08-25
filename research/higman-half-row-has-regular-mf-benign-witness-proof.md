---
rg: 2
id: higman-half-row-has-regular-mf-benign-witness-proof
kind: route
title: Turn the second half-row tower letter into a central HNN letter
target: higman-half-row-has-regular-mf-benign-witness
requires:
  - single-free-endomorphism-has-marked-finite-quotients
  - regular-mf-central-hnn-closure
artifacts:
  - GroupApproximation/Higman/RowDeletionBenign.lean
---

The first tower is the mapping torus of `xi_0` and hence is residually finite.
Since `xi_1=Ad(c^-1) o xi_0`, substitute `z=t_0^-1 c t_1`; the second HNN
relations become exactly `[z,F]=1`.  Apply regular central-HNN closure.  The
attached formal development already proves the intersection and finite
generation assertions which make this ambient group a benign witness for the
positive half-row.
