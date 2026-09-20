---
rg: 2
id: shared-records-obey-complementary-check-uncertainty
kind: claim
title: Shared complementary measurement records require noncommutativity for small disagreement
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
distinct_from:
  factorwise-complete-composition-returns-the-input-energy: That uses clause-private proofs and independent data blocks; this allows a shared record and arbitrary entanglement but constrains its complementary observables.
---

Let X,Z be data-qubit Paulis and Q_X,Q_Z Hermitian record involutions.
Set A=Z tensor Q_Z, B=X tensor Q_X and K=I/2-(A+B)/4.
For c=||[Q_Z,Q_X]||<=2, every joint state has energy at least
1/2-sqrt(2+c)/4. Energy <=eta<=1/2 requires
c>=max{0,2-16eta+16eta^2}.

Commuting records have the sharp floor (2-sqrt(2))/4, including
arbitrary data-record entanglement. Quantum records Q_Z=Z,Q_X=X
evade that floor: the Bell state has zero energy.
This excludes simultaneously readable classical predictions for both
checks, not arbitrary shared quantum proofs or Quantum PCP.

