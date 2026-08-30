---
rg: 2
id: stw95-one-zstable-factor-forces-pure-product
kind: claim
title: One Z-stable factor makes every minimal tensor product pure
distinct_from:
  stw95-af-factor-preserves-purity: that assumes an AF factor and purity of the other factor but need not produce Z-stability; this assumes one Z-stable factor and imposes no regularity at all on the other factor.
  split-cu-tensor-map-implies-pure-product: that is a Cu-level criterion for two pure factors; this proves C*-level Z-absorption directly without assuming the abstract-to-concrete Cu tensor map splits.
artifacts:
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
---

Let `A` and `B` be separable C*-algebras.  If either factor is Z-stable,
then

```text
A tensor_min B
```

is Z-stable and therefore pure.  No nuclearity, exactness, simplicity, or
pureness hypothesis is required on the other factor.

Consequently a counterexample to the pure-tensor permanence part of Problem
XCV must have **both** pure factors non-Z-stable.  This removes the nuclearity
qualification from the previously recorded Z-absorbing positive class and
shows that nonexact tensor kernels cannot obstruct purity once either factor
absorbs `Z`.
