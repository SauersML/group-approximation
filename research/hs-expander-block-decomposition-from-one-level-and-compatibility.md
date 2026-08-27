---
rg: 2
id: hs-expander-block-decomposition-from-one-level-and-compatibility
kind: route
title: Build the Leavitt nested decomposition from one-level Kun blocks and synchronization
target: hs-expander-block-decomposition
requires: [hs-one-level-expander-block-decomposition, leavitt-hs-block-compatibility]
---

Apply `hs-one-level-expander-block-decomposition` first to the explicit
Kazhdan ambient group `G=EL_D(R)` and then to its Kazhdan subgroup
`Gamma=EL_alpha(R)` in the Leavitt compression configuration.  Restricting a
`delta`-almost representation of `G` to `Gamma` preserves the normalized-HS
defect bounds on the fixed word packet, so the two applications give coarse
and fine one-level partitions with errors tending to zero and fixed positive
block-gap constants.

These independent partitions need not be nested and need not be transported
by the prefix compressors; that is exactly the hypothesis supplied by
`leavitt-hs-block-compatibility`.  Apply it to replace the two partitions on a
further `o(1)`-trace corner so that

```text
B_G <= B_Gamma
```

and every fine atom is carried by `phi(u)` and `phi(v)` to a single fine atom
up to `o(1)` normalized-HS error with no asymptotic trace loss.  By the claim,
the replacement preserves positive dimension-independent coarse and fine
Poincare gaps and adds only `o(1)` generator boundary.

Take the maximum of the finitely many error moduli and the minimum of the
surviving positive gap constants.  The resulting common near-full projection,
nested coarse/fine block algebras, gap inequalities, and two compressor drift
bounds are exactly the clauses of `hs-expander-block-decomposition`.
