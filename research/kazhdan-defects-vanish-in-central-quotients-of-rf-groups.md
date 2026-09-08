---
rg: 2
id: kazhdan-defects-vanish-in-central-quotients-of-rf-groups
kind: claim
title: Every Kazhdan compression defect is trivial in a central quotient of a residually finite group
distinct_from:
  central-quotients-of-residually-finite-groups-are-mf: that is the construction of the approximate models and the MF conclusion, and consumes no analytic input; this feeds those models to the Kazhdan transport collapse and concludes about the defect subgroup.
  mf-group-with-finite-central-compression-defect: that exhibits an MF group whose compression defect retains a finite central subgroup, with the compressed subgroup infinite cyclic and NOT Kazhdan; this shows that under the property-(T) hypothesis the same cannot happen in a central quotient of a residually finite group, so the two are complementary and the (T) hypothesis is exactly what separates them.
  finite-order-central-compression-defect-survives-mf: that is the second such witness, again with an infinite cyclic compressed subgroup; the same complementarity applies.
  defect-forces-proper-self-embedding: that is the algebraic constraint saying a nontrivial defect forces a proper self-embedding of the core; this removes an entire supply of cores that satisfy that constraint, namely those arising as central quotients of residually finite groups.
artifacts:
  - research/artifacts/central-quotient-rf-exclusion-2026-09-08.md
---

**ESTABLISHED.**  Let `Lambda` be countable and residually finite, let
`Z <= Z(Lambda)`, and put `G = Lambda/Z`.  Then for every subgroup
`L <= G` with property (T),

```text
D_G(L) = {1},                                                     (CQ3)
```
where `D_G(-)` is the intrinsic compression-centralizer defect of
`intrinsic-compression-defect-functoriality-and-saturation`.

**The property-(T) hypothesis is exactly the dividing line.**  Without it
the conclusion is false even for a central defect of order two:
`mf-group-with-finite-central-compression-defect` and
`finite-order-central-compression-defect-survives-mf` both exhibit an MF
group whose compression defect retains a nontrivial finite central
subgroup, with the compressed subgroup infinite cyclic.

**What this excludes.**  `defect-forces-proper-self-embedding` shows a
nontrivial defect needs a core that embeds properly in itself, and that
co-Hopfian cores are useless; non-Hopfian Kazhdan groups are therefore the
natural supply.  `(CQ3)` removes every such group that is a central
quotient of a residually finite group — in particular the standard
finitely presented family, by
`cornulier-non-hopfian-kazhdan-groups-are-mf`.

This is an exclusion, not a construction.  It settles nothing about
`locally-finite-defect-subgroup-dies-in-every-corona`, and produces no
non-MF group.

DERIVATION
central-quotient-kazhdan-defect-vanishing-proof
