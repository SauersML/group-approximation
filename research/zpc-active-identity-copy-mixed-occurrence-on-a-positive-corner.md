---
rg: 2
id: zpc-active-identity-copy-mixed-occurrence-on-a-positive-corner
kind: claim
title: Authenticate active and identity-label controlled actors on one positive finite-matrix corner
distinct_from:
  pauli-gauge-word-retains-and-cocycle: that proves packet dressing cannot create the identity-label copy; this asks for a genuinely new model-dependent mixed occurrence.
  transitive-selector-flips-kill-leavitt-sibling-support: that rules out rank-preserving selector transport; this permits a one-sided proper-corner or cross-Gram incidence which does not transport the selector atom.
  zpc-controlled-pauli-and-hs-shared-gauge-lock: that is the full gauge-lock dichotomy; this isolates the smallest same-reservoir occurrence which would supply its missing ingredient.
  reynolds-exit-does-not-carry-pauli-gauge: that proves the existing index-two proper section exposes payload only on its source and used range; this asks for a new section or mixed Gram sourced on the exit itself.
  character-hnn-retains-and-or-holonomy: that proves a common finite-character edge preserves the controlled cocycle while separate edges retain arbitrary holonomy; this asks for the extra mixed occurrence controlling that relative stable word.
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

The two occurrence estimates are not sufficient while their frames are
independent. `separate-occurrence-arrows-do-not-lock-pauli-gauge` gives an
exact finite Clifford model with `R=E_11`, `c=1`, and zero defect in
`(AIM1)--(AIM2)`, yet the original multiplicity actors have commutator `-1`:
the two arrows separately rotate both actors to the same commuting Pauli
axis. The packet must therefore add a **joint-frame** relation--one common
arrow, or a mixed Gram constraint controlling `W_A^*W_B` on `R`. With that
coherence added, `(AIM1)--(AIM2)` would make the residual commutator in
`(CPM6)` asymptotically trivial on a positive fraction of the active atom;
iteration or a bounded packing argument would still be needed if `c<1`.

Packet dressing cannot supply `(AIM1)` by
`pauli-gauge-word-retains-and-cocycle`.
Rank-preserving selector flips cannot supply it by
`transitive-selector-flips-kill-leavitt-sibling-support`.  Sector-preserving
covariance leaves the exact absorber of
`leavitt-crossed-gram-pauli-charge-has-sectorwise-escape`, while a fixed whole
finite-packet type meets the regular-profile barrier.  The required input is
therefore specifically matrix-origin occurrence information.

The first proper-corner instantiation is now fenced as well.
`reynolds-exit-does-not-carry-pauli-gauge` shows that the index-two Reynolds
construction places the assignment mass in the unused range, while all
available same-range dressings recover their relative gauge on the
complementary source and used range.  The next live construction must start
on a positive piece of that exit; naming its mass is not enough.

Exact finite-character transport does not bypass this requirement.
`character-hnn-retains-and-or-holonomy` shows that transporting the packet
with one edge preserves the AND cocycle, while transporting actors separately
leaves an arbitrary compressed relative stable word.  The remaining seam is
therefore a genuinely mixed row, not another atom-transport theorem.
