---
rg: 2
id: qubit-pairs-have-half-gap-and-unbounded-rounder-cost
kind: claim
title: One-local projector pairs have half combinatorial gap and quadratic optimal rounder cost
invalidates:
  - qpcp-rounder-from-combinatorial-soundness-alone
artifacts:
  - research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md
  - scripts/check_qpcp_rounding.py
  - research/artifacts/qpcp-rounding-exact-certificate-2026-09-07.json
distinct_from:
  coherent-shear-is-combinatorially-invisible: that uses a frustration-free chain and requires preservation of endpoint marginals; this has positive combinatorial gap one half and obstructs arbitrary exact rounders without any input-preservation requirement.
  combinatorial-gap-and-rounder-give-energy-gap: that is the abstract optimal-cost identity; this supplies an explicit bounded-occurrence rational projector family with constant combinatorial gap and vanishing normalized energy.
---

For every integer `N >= 1`, place the pair
`P = |1><1|`, `Q_N = w_N w_N^*`,
`w_N = (2N,N^2-1)^T/(N^2+1)` on each of `N` qubits, and normalize the
sum of these `2N` terms by `2N`. Each term is a norm-one projector, locality
is one, the qudit dimension is two, and each qubit occurs twice. Entries
have `O(log N)`-bit rational descriptions. Then

```text
s* = N,    beta = 1/2,    lambda_min(H_N) = 1/(N^2+1),
C_min(H_N) = (N^2+1)/2.
```

The rounder definition is the unrestricted CPTP instrument in
`combinatorial-gap-and-rounder-give-energy-gap`. In particular no faithful
preservation of input data is assumed. Thus combinatorial soundness and
bounded local incidence alone do not give a uniform rounder constant.

This elementary family is easy to solve and does not refute QPCP or exclude
a specially designed amplifier. Its term matrices depend on `N`, despite
its fixed qudit dimension. The proof is ordinary mathematics with exact
algebraic replay, not a Lean certificate or a claim of new projection theory.
