---
rg: 2
id: paid-t00-row2-source-incidence-proof
kind: route
title: Separate the paid and signed-source summands in an exact finite packet
target: paid-t00-carrier-can-miss-row2-source
requires:
  - native-t00-y1-collision-pays-marked-opnorm
  - marked-t00-separation-has-gl10-model
  - center-chain-four-hecke-flags-have-native-ranks
  - row2-marked-center-action-return-has-gl8-model
  - row2-parallel-a2-return-diamond-has-gl8-model
---

The roots in `(PRS1)` have positions `(7,8)`, `(1,3)`,
`(6,5),(5,4),(4,2)`, and `(9,4),(9,2)`.  The ordinary Steinberg
commutator criterion proves that `D` and `z` commute with `H` and `U`.
Therefore all four spectral/group-algebra projections in `P_pay r_2`
commute.

For the first finite block, append vertices `r,s` to the exact marked
`GL_10(F_2)` table and make the assignments `(PRS3)`.  Ordinary
transvection multiplication gives both source roots and the full
`UT_4(F_2)` center chain.  In the permutation representation on the 4096
vectors of `F_2^12`, the normalized trace of a group element is the fraction
of fixed vectors.  Expanding

```text
e_chi z_U=(1/256) sum_(g in H,u in U) chi(g)gu
```

and computing each fixed-space dimension gives zero.  The MSI artifact does
this with exact integer arithmetic and also rechecks the entire inherited
row-two table.

For the second block, the three-qubit Pauli and CNOT identities
`(PRS6)--(PRS8)` are direct conjugation calculations.  The representation
of `H` factors through its abelianization by sending each simple generator
to `h`; consequently its `chi`-projection is exactly `(1-h)/2`.  The source
group `U` acts trivially, so this is also `r_2`.  Since `h=Dz`, equations
`(PRS5)` and the stated ranks follow from the joint `Z_1,Z_3` eigenbasis.

All named relations hold blockwise and hence on their direct sum.  The first
block makes `A_2` nonidentity but has zero signed source; the second makes
the source and paid carrier nonzero and orthogonal.  This proves `(PRS2)`
for the union while preserving every displayed finite-table hypothesis.

This argument fixes `Q=e_chi z_U`.  Its ambient representation may have an
arbitrary reducible profile, but the source projector itself is not
quantified over the other profile-dependent alternatives in the selector
type menu.
