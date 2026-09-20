---
rg: 2
id: tracial-local-witness-control-counterexamples
kind: route
title: Rank-one states and CNOT fanout separate tracial algebra control from local witness verification
target: tracial-internality-does-not-supply-local-witness-control
requires: []
artifacts:
  - research/artifacts/qpcp-integration-ledger-2026-09-20.md
---

A rank-one projection has exactly one nonzero eigenvalue. Its normalized
trace is `1/D`, while its range vector has energy one in `P_D` and zero
in `I-P_D`. This proves both trace counterexamples.

If `A<=CB`, positivity of trace gives the all-state inequality. Conversely,
testing every pure state forces every quadratic form of `CB-A` to be
nonnegative, which is exactly operator positivity. For the norm conversion,
`rho<=||rho||I` gives
`Tr(rho X*X)<=||rho||Tr(X*X)=D||rho|| ||X||_(2,D)^2`.
Take `rho=X=P_D` to attain equality with coefficient `D`.

Each CNOT from qubit one to target `j` conjugates `X_1` to `X_1 X_j`.
Their product conjugates `X_1` to the full Pauli string, which is nonidentity
on every site. Arbitrary unitary conjugation preserves the stated abstract
and tracial data; the site support therefore cannot be inferred from those
data alone. The integrated ledger explains the group-to-QMA interface
without importing any nonhyperlinearity theorem into this elementary proof.
