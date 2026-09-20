---
rg: 2
id: regular-graph-parity-has-uniform-single-defects
kind: claim
title: Regular-graph parity instances have energy one over the term count and uniformly distributed single defects at every arity
artifacts:
  - research/artifacts/qpcp-strengthened-amplification-2026-09-20.md
  - research/artifacts/check-qpcp-strengthened-amplification-2026-09-20.py
  - research/artifacts/qpcp-strengthened-amplification-replay-2026-09-20.json
distinct_from:
  factorwise-complete-composition-returns-the-input-energy: that is a quantum private-proof composition bound; this supplies classical diagonal input families at every fixed arity, including odd arity, with an exact uniform defect distribution.
---

For every integer `r>=2` and every sufficiently large even `m>r`, there
is an explicit connected simple `r`-regular graph on `m` vertices. Put a
Boolean variable on each edge and impose incident-edge parity zero at
every vertex except vertex zero, whose charge is one. Let `h_v` be the
violation projector and `H=(1/m)sum_v h_v`.

Then `e(H)=1/m`, and an explicit distribution of assignments violates each
specified constraint with probability exactly `1/m`. Each term acts on
exactly `r` qubits, each variable occurs in exactly two terms, and flipping
any incident bit repairs a violated predicate.

Taking `r=k_0` in the FCC lemma removes the old even-arity loss: its output
energy is at most `eta_m+1/m`. With the strengthened global-walk bound,
this forces universal FCC soundness loss `L>=(t+1)/2` whenever
`m eta_m->0`. The Hamiltonians here are diagonal and easily solved;
no QMA-hardness assertion is made about this family.
