---
rg: 2
id: normal-kazhdan-kernel-cannot-live-in-amenable-edge-tree
kind: claim
title: A torsion-free group with a nontrivial minimal amenable-edge tree action has no nontrivial normal Kazhdan subgroup
distinct_from:
  titz-witzel-soficity-is-one-finite-csp: That seeks permutation models for a Kazhdan group which has property FA; this excludes manufacturing the desired normal Kazhdan kernel by sofic amalgam or HNN permanence.
  literal-mf-radical-has-no-infinite-kazhdan-subgroup: That uses the particular Clifford-block Bass--Serre decomposition of the literal MF radical; this is an abstract normal-subgroup theorem for every minimal tree action with amenable edge stabilizers.
artifacts:
  - research/artifacts/alternate-sofic-kernel-audit-round3-2026-08-26.md
---

Let a group `G` act minimally and without a global fixed point on a
nontrivial simplicial tree `T`.  Assume every edge stabilizer is amenable.
Then every normal property-`(T)` subgroup `K normal G` is finite.  If the
edge stabilizers are torsion-free (in particular, if `G` is torsion-free),
then

```text
K=1.                                                     (AKT1)
```

Consequently none of the standard soficity constructions by a nondegenerate
free product with amalgamation or HNN extension over an amenable subgroup can
itself be the requested torsion-free group with a nontrivial normal Kazhdan
MF radical.  This applies in particular to Kar--Nikolov's finitely presented
sofic non-LEA group

```text
SL_n(Z[1/p]) *_Z SL_n(Z[1/p]).                           (AKT2)
```

Its two Kazhdan vertex groups are not normal, and it has no nontrivial normal
Kazhdan subgroup at all.  Replacing the vertex groups by torsion-free
finite-index congruence subgroups does not repair the normal-kernel problem:
the Bass--Serre edge remains cyclic and the same theorem applies.

DERIVATION
normal-kazhdan-kernel-amenable-edge-tree-proof
