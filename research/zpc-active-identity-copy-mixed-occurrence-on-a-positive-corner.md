---
rg: 2
id: zpc-active-identity-copy-mixed-occurrence-on-a-positive-corner
kind: claim
title: Authenticate active and identity-label controlled actors on one positive finite-matrix corner
distinct_from:
  pauli-gauge-word-retains-and-cocycle: that proves packet dressing cannot create the identity-label copy; this asks for a genuinely new model-dependent mixed occurrence.
  transitive-selector-flips-kill-leavitt-sibling-support: that rules out rank-preserving selector transport; this permits a one-sided proper-corner or cross-Gram incidence which does not transport the selector atom.
  zpc-controlled-pauli-and-hs-shared-gauge-lock: that is the full gauge-lock dichotomy; this isolates the smallest same-reservoir occurrence which would supply its missing ingredient.
---

**OPEN MIXED-OCCURRENCE SEAM.**  After fixed packet exactification, construct
on the active-mismatch atom `E_11` a model-dependent reducing projection
`R<=E_11` and identity-label actors `A^o=I tensor A^o_gauge`,
`B^o=I tensor B^o_gauge` such that, with dimension-free constants,

```text
tau(R)>=c tau(E_11)-C defect,

||R(A^o-W_A A_11 W_A^*)||_2
 + ||R(B^o-W_B B_11 W_B^*)||_2 <=C defect,             (AIM1)

||R([A^o,B^o]-1)||_2 <=C defect.                       (AIM2)
```

Here `W_A,W_B` are the allowed occurrence identifications and the construction
must not unitarily transport `R` to another selector atom.  Equivalently, a
non-rank-preserving cross-Gram or one-sided proper-corner incidence must
authenticate the active actors and commuting-label actors on the same
multiplicity reservoir.

Equations `(AIM1)--(AIM2)` would make the residual commutator in `(CPM6)`
asymptotically trivial on a positive fraction of every active-mismatch atom;
the controlled-Pauli relation would then charge that atom.  Iteration or a
bounded packing argument would still be needed if `c<1`.

Packet dressing cannot supply `(AIM1)` by
`pauli-gauge-word-retains-and-cocycle`.
Rank-preserving selector flips cannot supply it by
`transitive-selector-flips-kill-leavitt-sibling-support`.  Sector-preserving
covariance leaves the exact absorber of
`leavitt-crossed-gram-pauli-charge-has-sectorwise-escape`, while a fixed whole
finite-packet type meets the regular-profile barrier.  The required input is
therefore specifically matrix-origin occurrence information.
