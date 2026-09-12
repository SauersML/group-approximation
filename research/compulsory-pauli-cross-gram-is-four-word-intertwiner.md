---
rg: 2
id: compulsory-pauli-cross-gram-is-four-word-intertwiner
kind: claim
title: The compulsory Pauli cross-Gram overlap carries all four PI words
refuted_by:
  - local-rectangular-refutes-cross-gram-pi
distinct_from:
  pauli-overlap-yields-positive-spectral-corner: that proves only a positive cross-Gram mass and explicitly supplies no holonomy or common-word intertwining.
  one-common-intertwiner-carries-the-four-pauli-pi-bridge: that asks for a near-unitary full-corner map; this uses the already forced positive-mass cross-Gram contraction and requires no polar extension outside its support.
---

**REFUTED AS A LOCAL-PACKET CLAIM.**  In every sufficiently accurate canonical microstate of the fixed
raw/comb Pauli packet, choose the heavier ordered overlap

```text
T=X_j^*X_i,
||T||_2^2>=5/64-o(1),                                 (PCG1)
```

from `pauli-overlap-yields-positive-spectral-corner`.  On the support of
this same contraction, decode four source contractions `C_1,...,C_4` in one
exactified `M_2 tensor I` algebra and the four transverse two-qubit target
words `D_1,...,D_4` so that

```text
sum_(k=1)^4||D_kT-TC_k||_2=o(1),                      (PCG2)
||s4(D)-8D_1D_2D_3D_4||_2=o(1).                      (PCG3)
```

Every error must be bounded by a dimension-independent modulus of the fixed
packet defect.  The same orientation and the same `T` must be used in all
four rows; separate hard/comb branch transports are excluded by
`separate-pauli-branch-transports-do-not-carry-s4`.

This is strictly weaker than recovering a full-support common unitary.  The
fixed mass in `(PCG1)` is already enough for the terminal contradiction.
The remaining content is one mixed-word identity coupling the compulsory
overlap to both transverse Pauli pairs.

The exact canonical rectangular model satisfies all of the local hypotheses
but forbids every positive-mass common intertwiner.  The corrected frontier
is `atlas-kernel-relators-couple-cross-gram-to-four-pauli`, which explicitly
uses the full regular-Atlas kernel packet and requires a nonlocal mixed row.
