---
rg: 2
id: fanizza-heat-filter-compressor-route
kind: route
title: Return the explicit Fanizza heat filter through one matrix-only compressor
target: fanizza-native-signal-groupification
requires:
  - two-copy-bcs-game-hamiltonian-dominates-fanizza-signal
  - fanizza-heat-filter-has-uniform-cstar-decay
  - kleene-completeness-needs-only-a-nontrivial-exact-representation
  - fanizza-heat-filter-one-sided-return
---

Work in the two-copy native variable group and retain the explicit rational
positive contraction

```text
K_m=1-H_m.
```

Fanizza soundness already gives uniform decay of `D_R K_m^t` in every
nonmember representation, while a perfect HALT vector makes every filtered
element act as the same nonzero signal.  Construct one finite ordinary-group
return cell which, after finite-matrix packet compression, identifies a fixed
marked carrier with arbitrarily deep `K_m`-filtered carriers.  Countable
infinite amplification may realize the return exactly on the HALT witness;
finite matrices must pay the decay estimate.

This route does not require a generic Boolean predicate packet, a cyclic
context atlas, or a raw Turing tape.  Its sole missing theorem is
`fanizza-heat-filter-one-sided-return`.
