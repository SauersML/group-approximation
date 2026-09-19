---
rg: 2
id: raw-unitary-traffic-gauge-instability
kind: claim
title: Raw unitary traffic moments are maximally gauge-unstable even on an exact regular table
---

Let `g` generate `C_2` and let `P` be the `2 x 2` permutation matrix of its
regular action.  For every `t in [-1,1]` there is a unitary `Q` such that
`U = Q P Q^*` is still an exact regular-character representation of `C_2`,
but the plain graph-indexed moment of the two-edge fork with one edge labelled
`g` and the other labelled by the identity equals `t`.

For the actual permutation matrix `P`, the same fork is a tree and its moment
is exactly `1`.  Thus the deviation can be as large as `2` at zero
multiplicative defect and with exactly the correct regular trace.

Consequently the direct entrywise construction suggested as the first attempt
in `traffic-branching-rounding-hierarchy` cannot work in any simultaneous-
conjugation-invariant formulation.  A successful traffic route must introduce
and synchronize additional classical structure (a basis/Cartan, POVM,
point-cloud, relative distribution, or equivalent hidden state) rather than
read the raw branching graph polynomial from the unitary matrices.
