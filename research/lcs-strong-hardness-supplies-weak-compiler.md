---
rg: 2
id: lcs-strong-hardness-supplies-weak-compiler
kind: route
title: Forget efficiency and replace quantum completeness by commuting completeness
target: perfect-completeness-constant-soundness-lcs-compiler
requires:
  - lcs-perfect-quantum-completeness-re-hardness
artifacts:
  - research/artifacts/hyperbolic-and-perfect-lcs-campaign-2026-09-20.md
---

For each input, enumerate the finite random strings and questions of the
polynomial-time sampler and output its finite LCS table, retaining only
positive-probability sampled constraints and their associated variables.
This gives full support on the chosen constraints, as required to identify
perfect commuting value with the nontrivial solution-group sign. This is
a total computable operation; it need not be polynomial in input length. On halting
inputs omega_q=1 implies omega_qa=1 and hence omega_qc=1. On nonhalting
inputs the uniform upper bound s<1 supplies the older strict-soundness
promise. These are exactly that weaker target's two clauses.

No reverse implication follows: a fixed game with qc value one and qa value
less than one supplies the weak target by a constant map, but fails quantum
completeness on every halting input.
