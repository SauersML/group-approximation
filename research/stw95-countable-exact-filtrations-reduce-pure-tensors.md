---
rg: 2
id: stw95-countable-exact-filtrations-reduce-pure-tensors
kind: claim
title: Exact tensoring reduces pure permanence through continuous countable filtrations
artifacts:
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
distinct_from:
  stw95-exact-finite-ideal-filtration-reduction: that performs only finite induction; this permits every continuous filtration indexed by a countable ordinal and handles limit stages by purity of sequential inductive limits.
---

Let `B` be exact.  Let `(I_alpha)_(alpha<=gamma)` be a continuous increasing
filtration of a C*-algebra `A` by closed ideals, indexed by a countable
ordinal, with

```text
I_0=0,                 I_gamma=A,
I_lambda=closure(union_(alpha<lambda) I_alpha)
```

at every limit ordinal.  If

```text
(I_(alpha+1)/I_alpha) tensor_min B
```

is pure for every successor stage, then `A tensor_min B` is pure.

Consequently, if exact algebras `A` and `B` have continuous countable
composition series and the tensor product of every pair of their simple
successor quotients is pure, then `A tensor_min B` is pure.
