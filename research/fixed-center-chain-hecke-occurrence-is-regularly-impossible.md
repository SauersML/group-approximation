---
rg: 2
id: fixed-center-chain-hecke-occurrence-is-regularly-impossible
kind: claim
title: A fixed exact occurrence row on the center-chain Hecke flags contradicts the regular trace
invalidates:
  - center-chain-hecke-flags-to-native-cross-gram
distinct_from:
  exact-whitehead-selector-gauge-attachment-collapses-packet: that treats two exact selector attachments on a full finite-packet isotypic carrier; this applies the same tracial firewall to the proposed fixed group-algebra Hecke subcorner.
  center-chain-hecke-polar-supports-are-nested-pauli-flags: that exact Hecke calculation remains valid; this refutes only its promotion to the two native unequal-scale selector occurrences by a fixed ordinary-word row.
  binary-leavitt-native-two-scale-cross-gram-positive: that permits a representation-dependent finite-matrix polar cut with loss charged by approximate word defects; this rules out replacing that finite-only cut by the fixed exact Hecke projections.
---

**ESTABLISHED REFUTATION OF THE FIXED-ROW PROMOTION.**  Retain the exact
group-algebra projections from the center-chain calculation,

```text
e=e_chi,             p_1=ez_1,             p_2=ez_2<=p_1.
```

In the canonical group trace they have

```text
tau(e)=1/64,         tau(p_1)=1/256,        tau(p_2)=1/512. (FCH1)
```

In particular the proposed common carrier is a fixed nonzero projection in
the group von Neumann algebra, not a matrix-coordinate spectral cut which
can disappear in the left regular representation.

Suppose the finite ordinary-word row requested by
`center-chain-hecke-flags-authenticate-native-occurrences` existed.  By its
statement, after only fixed finite label relabelings, the two prescribed
native selector covariances would restrict to this fixed positive Hecke
carrier, their label cuts would have relative traces `1/4` and `1/8`, and
the relative polar gauge would lie in the common source-Pauli commutant.
Thus the two multiplicity involutions would have one unitary-conjugacy class
on the nonzero common corner.  Normalize the canonical trace on that corner
and write `theta` for their common positive spectral fraction.

The first selector row has source/target fractions `(1/2,1/4)`.  The exact
affine selector trace formula therefore gives

```text
1/2=3/4-theta/2,             hence theta=1/2.          (FCH2)
```

The next-refinement row has fractions `(1/4,1/8)`, and the same formula gives

```text
1/4=7/8-3theta/4,            hence theta=5/6.          (FCH3)
```

Equations `(FCH2)--(FCH3)` contradict each other in every finite tracial
corner.  This is exactly the tracial calculation behind
`two-shared-gauge-selector-rows-have-an-affine-rank-obstruction`; it does not
use finite-dimensionality.  Applying it in the left regular representation
would force the common Hecke carrier to be zero, contrary to `(FCH1)`.

Consequently no fixed exact ordinary-word row can identify these two Hecke
polar maps with the two native unequal-scale selector occurrences in the
sense requested by the invalidated claim.  The nested support, cross-Gram,
and mixed-Pauli identities of
`center-chain-hecke-polar-supports-are-nested-pauli-flags` remain correct and
potentially useful.  What they cannot supply is the missing authentication:
that step must be genuinely finite-matrix-only, with a
representation-dependent cut and discarded mass controlled by approximate
word defects.  No Property `(T)` or Kazhdan input is used in this refutation.
