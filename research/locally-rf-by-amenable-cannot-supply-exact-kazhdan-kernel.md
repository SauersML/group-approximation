---
rg: 2
id: locally-rf-by-amenable-cannot-supply-exact-kazhdan-kernel
kind: claim
title: Every Kazhdan subgroup of a locally residually finite by amenable group is residually finite
distinct_from:
  exact-kazhdan-radical-kernel-cannot-be-lef: That excludes a LEF Kazhdan kernel with no finite quotients; this excludes Kazhdan subgroups of an ambient class containing important finitely presented sofic non-LEA groups.
  mapping-torus-mf-radical-lies-in-finite-residual: That forces the requested kernel to have no finite quotients; this supplies the incompatible residual-finiteness conclusion for the locally-RF-by-amenable candidate class.
---

Suppose

```text
1 -> L -> H -> A -> 1
```

is exact, `L` is locally residually finite and `A` is amenable.  Then every
property-`(T)` subgroup `K<=H` is residually finite.  In particular, if `K`
has no nontrivial finite quotient, then

```text
K=1.                                                     (LRA1)
```

This rules out the isolated finitely presented sofic non-LEA group in
Cornulier, *A sofic group away from amenable groups*, and every group obtained
from the same locally-RF-by-abelian mechanism, as an ambient source of the
requested exact Kazhdan MF-radical kernel.

DERIVATION
locally-rf-by-amenable-kazhdan-subgroup-proof

