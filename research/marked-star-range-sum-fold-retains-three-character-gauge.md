---
rg: 2
id: marked-star-range-sum-fold-retains-three-character-gauge
kind: claim
title: The object-erasing range-sum fold leaves a three-character gauge on the outer-corrected marked star
artifacts:
  - research/marked-star-range-sum-three-character-proof.md
distinct_from:
  marked-star-outer-corrected-whiteheads-are-quarter-swaps: that constructs the two literal outer-corrected adjacent-cell transports and finds their common quarter label; this adjoins the smallest object-erasing binary range-sum occurrence to those same two chart edges.
  closed-compression-fold-loop-retains-s3-gauge: that gives a three-character model for the compression-preimage and fold table with separate Pauli payload factors; this identifies the two chart-edge transpositions with the reservoir factors of the positive marked-star transports.
  payload-range-sum-whitehead-has-three-character-model: that authenticates the inverse and reverse payload commutators but does not contain the three distinct-center marked-star packet; this preserves all three anchored Pauli pairs and both adjacent-cell covariances.
  star-attached-completeness-fold-splits-off-p-corner: that literally identifies the q branch and its opposite root with the finite projective marked-star head and finds a zero-full-Hecke-source profile; this smaller compressed-label audit identifies instead the surviving three-character holonomy on the two outer-corrected chart edges.
  binary-branch-flip-weyl-has-s3-c2-model: that also adjoins the full opposite-root branch exchange and obtains an extra independent swap; this treats the smaller object-erasing fold before that exchange.
  binary-leavitt-two-shared-gauge-selector-compiler: that needs an unequal one-quarter/one-eighth label pair or two unequal source-to-quarter rows; this exact model retains two quarter labels and equal-rank fold signs.
---

Adjoin to the outer-corrected marked-star packet the smallest binary
range-sum occurrence table.  After a spare-index placement disjoint from
the outer Weyls, write its parent and two child signs as

```text
D,C_0,C_1,                 C_0C_1=D,                  (MSF1)
```

and attach the two branch chart edges by

```text
U_1 D U_1^(-1)=C_0,       U_2 D U_2^(-1)=C_1.        (MSF2)
```

Here `(MSF1)` is the same-output-root form of
`s_0t_0+s_1t_1=1`; it is the object-erasing row of
`leavitt-range-sum-fold-is-first-object-erasing-row`.  Equations `(MSF2)`
are the output-level branch attachments after the fixed outer correction,
which commutes with the fold placement.

This complete compressed occurrence table has an exact `24`-dimensional
marked model.  On

```text
H=(C^2)^(tensor 3) tensor C^3
```

use the standard three Pauli pairs on the first factor, and put

```text
D  =I_8 tensor diag( 1,-1,-1),
C_0=I_8 tensor diag(-1,-1, 1),
C_1=I_8 tensor diag(-1, 1,-1),                         (MSF3)

U_1=SWAP_(1,2) tensor (0 2),
U_2=SWAP_(2,3) tensor (0 1).                          (MSF4)
```

The star center and mark are `-I` on this compressed carrier.  The two
operators in `(MSF4)` swap the adjacent anchored Pauli pairs, are
involutions, and satisfy the braid.  The transpositions in `(MSF4)` send
`D` to `C_0,C_1`, while `(MSF3)` gives `C_0C_1=D`.  Thus every star
covariance and every displayed fold/branch row is exact with nonzero marked
carrier.

The fold does not supply the missing unequal selector typing.  Its three
signs are conjugate and all have negative fraction `2/3`.  Its two chart
gauges are the two conjugate transpositions of the same `S_3` reservoir.
On the eight-dimensional star label, both transports remain adjacent swaps
of negative fraction `1/4`.  More generally every word in the enlarged
table factors as

```text
(Pauli_3 semidirect S_3)_label tensor (signed S_3)_reservoir. (MSF5)
```

The label factor still has determinant one, so no involutory word in this
table has the rank-one `1/8` label reflection.  Adding arbitrary copies of
the trivial reservoir orbit changes the common fold-sign rank but changes
all three signs equally; it cannot manufacture source fractions `1/2` and
`1/4` on the two conjugate chart edges.

Consequently the first object-erasing Leavitt row does not escape the
marked-star determinant/rank fence.  It promotes the free reservoir factors
to a concrete three-character holonomy but neither produces a one-eighth
label nor distinguishes two source ranks.  This is a scoped exact model of
the compressed star/fold occurrence table, not a representation of the full
binary-Leavitt Steinberg group.  A successful continuation must use an
additional coefficient-sensitive occurrence which leaves the quotient in
`(MSF5)`, such as an asymmetric payload return; the symmetric opposite-root
branch flip is already fenced by
`binary-branch-flip-weyl-has-s3-c2-model`.

No Property `(T)`, Kazhdan input, canonical trace, literature theorem,
local heavy computation, or Lean compilation is used.

DERIVATION
marked-star-range-sum-three-character-proof
