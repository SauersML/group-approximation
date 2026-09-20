---
rg: 2
id: tracial-internality-does-not-supply-local-witness-control
kind: claim
title: Tracial norm estimates and abstract commutants alone do not certify all-state energy domination or tensor-site locality
artifacts:
  - research/artifacts/qpcp-integration-ledger-2026-09-20.md
distinct_from:
  kazhdan-commutants-are-internal: that identifies an entire relative commutant in a fixed tracial matrix ultraproduct; this gives finite-dimensional counterexamples to substituting trace estimates or abstract algebra structure for all-state energy and prescribed tensor support.
  gap-and-floor-do-not-force-compatible-syndrome-effects: that separates an ordinary energy floor from compatible syndrome measurements; this concerns the earlier transfer from normalized trace and unitary-invariant algebra data to arbitrary witnesses and specified tensor sites.
---

For a rank-one projection `P_D` on dimension `D`,
`tr_D(P_D)=1/D` but `sup_rho Tr(P_D rho)=1`, and
`tr_D(I-P_D)=1-1/D` but `lambda_min(I-P_D)=0`.
Thus small normalized-trace error and large tracial energy do not imply
small error in every state or a ground-energy floor.

For Hermitian `A,B`, the inequality `Tr(A rho)<=C Tr(B rho)` for every
state is equivalent to `A<=CB` in operator order. Conversion from the
normalized Hilbert–Schmidt norm to state-weighted norm gives
`||X||_(2,rho)^2<=D ||rho|| ||X||_(2,D)^2`; the dimension factor is
sharp for pure states. It may be exponential in the number of qubits.

Global unitary conjugation preserves traces, spectra, norms and algebraic
commutants, but a CNOT fanout conjugates one-site `X_1` to
`X_1...X_n`. Unitary-invariant algebra data alone cannot establish bounded
support in a prescribed tensor decomposition.

These are specific failed inferences, not a proof that group methods can
never help quantum PCP. Applying Liu's internality and Thom's normalization
to local witness verification still needs a finite efficient compiler with
all-state estimates, specified support, completeness, and resource bounds.
