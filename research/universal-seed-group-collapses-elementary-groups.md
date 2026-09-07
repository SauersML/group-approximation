---
rg: 2
id: universal-seed-group-collapses-elementary-groups
kind: claim
title: One fixed group carries the ring obstruction for every full-defect ring and every rank at least two
distinct_from:
  full-defect-ring-non-mf-at-rank-two: that is the conclusion for each ring separately, with the rank-four calculation run on a finitely generated subring depending on that ring; this proves the obstruction once for one fixed group and transfers it, so no subring of the target is used.
  full-complementary-idempotent-elementary-full-mf-radical: that is the rank-four theorem over an arbitrary ring, and is the analytic input here; this fixes the ring and moves the conclusion by normal generation.
  elementary-rank-descent-to-two: that is the algebraic descent with no target class fixed; this instantiates it at one universal source and adds the MF conclusion.
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

Let `C` be the seed ring of `universal-split-pair-seed-ring` and put

```text
B = EL_4(C).
```

Then `B` is finitely generated and every homomorphism from `B` to an MF
group is trivial.  For every nonzero countable unital ring `R` with a
properly infinite unit and every `n >= 2` there is a homomorphism

```text
f : B --> EL_n(R)
```

whose image normally generates `EL_n(R)`.  Consequently every homomorphism
from `EL_n(R)` to an MF group is trivial.

So one compression calculation, performed once over `C`, gives the whole ring
family, and no passage to finitely generated subrings of `R` occurs.

**Formalization cost, recorded before adoption.**  `C` has characteristic
zero.  In this repository the Ershov--Jaikin-Zapirain input is unconditional
only in prime characteristic; the general case is reduced in
`PropertyT/EJZIntegralReduction.lean` to property (T) for
`EL_n(FreeAlgebra Z X)`, which is open, and `C` is a quotient of that free
algebra.  Routing the characteristic-two headline through `B` would make it
conditional on that residue, whereas it is unconditional today.  For the
manuscript the cost is nil, since Ershov--Jaikin-Zapirain is published for
every finitely generated ring.
