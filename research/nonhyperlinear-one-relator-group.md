---
rg: 2
id: nonhyperlinear-one-relator-group
kind: claim
title: A group with one defining relator is not hyperlinear
root: true
distinct_from:
  nonsofic-one-relator-group: That excludes permutation models; this excludes unitary models and is strictly stronger than the stated target.
  non-hyperlinear-group: That has specified finite-presentation witnesses; finite presentation does not give one defining relator.
  nonhyperlinear-hyperbolic-group: That imposes hyperbolicity, not a one-relator presentation; neither restriction is being inferred from the other.
artifacts:
  - research/artifacts/liu-new-frontiers-2026-09-20.md
---

OPEN. Exhibit a finitely generated one-relator group that is not
hyperlinear. A short many-relator presentation does not meet this target.

## Attempts

2026-09-20: a one-relator group with torsion is residually finite by the
existing Wise input, hence hyperlinear. The remaining torsion-free class
is locally indicable and has no nontrivial finitely generated Kazhdan
subgroup (`torsion-free-one-relator-has-no-kazhdan-subgroup`). Thus
embedding the Leavitt, Kun--Thom or lifted Kazhdan compression witnesses
is unavailable. A surjection onto one of them is insufficient because
hyperlinearity does not pass to arbitrary quotients.

The concrete research interface is now a trace-compatible Magnus HNN
construction, or a direct unitary obstruction in that construction;
the established permutation-side reductions in
`nonsofic-one-relator-group` provide constraints, not a unitary proof.
The positive compiler's locally indicable groups offer a separate
testbed for an obstruction without Kazhdan subgroups, but are not
claimed to be one-relator groups. The current bounded attempt closes
the unchanged compression-embedding route; no one-relator counterexample
or general group-to-one-relator transformation is asserted.
