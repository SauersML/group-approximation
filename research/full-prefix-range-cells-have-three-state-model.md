---
rg: 2
id: full-prefix-range-cells-have-three-state-model
kind: claim
title: Every finite binary prefix tree of one-arm range cells has a fixed three-state marked model
distinct_from:
  one-arm-range-sum-whitehead-has-marked-model: that gives one depth-one twelve-dimensional cell; this coherently addresses the same cell on a full binary tree of arbitrary depth and tests character collisions beyond the matrix dimension.
  local-morita-sibling-cells-have-a-two-qubit-periodic-absorber: that periodically reuses two Pauli factors without the coefficient range-sum row; this retains the literal parent-generation signs and the reverse-range crossed-zero row at every vertex.
  binary-leavitt-tagged-shift-table-has-centralizer-collisions: that uses private columns to evade a bounded-area chromatic centralizer fence; this gives an exact finite-state collapse of all losslessly conjugate prefix cells and identifies the additional cross-address holonomy a compiler would need.
artifacts:
  - research/full-prefix-three-state-model-proof.md
---

**ESTABLISHED EXACT FULL-TREE COUNTERMODEL.**  For every depth `N`, the
entire binary tree of losslessly addressed copies of the one-arm
range-sum/Whitehead cell has an exact unitary model on one fixed
twelve-dimensional space.  At every vertex `u` there is a parent sign
`J_u`, two range signs `C_(u,0),C_(u,1)`, two inverse Pauli pairs, and the
two addressed Whiteheads, with

```text
C_(u,0)C_(u,1)=J_u,
[X_(u,i),Z_(u,i)]=J_u,
[X_(u,0),Z_(u,1)]=[X_(u,1),Z_(u,0)]=1,                (FPT1)
W_(u,i)J_uW_(u,i)^(-1)=C_(u,i),
W_(u,i)X_(u,i)W_(u,i)^(-1)=X_(u,i).                   (FPT2)
```

The child sign is literally the next parent sign:

```text
J_(ui)=C_(u,i).                                        (FPT3)
```

Every cell at `u` is one simultaneous unitary conjugate of the fixed root
cell, so all remote discrepancies are losslessly addressed fixed
prototypes.  Different address words may have the same matrix value; this
is the harmless character collision exploited by the model.

The mixed reverse-range crossed-zero row does not remove the model.  Include
the actual coefficient relation

```text
e_(u,0)e_(u,1)=0
```

as the corresponding composable-root commutator between role copies of the
two range signs.  Those role copies commute exactly.  On the prescribed
`J_u=-1` atom, the two child negative supports are disjoint and exhaust the
parent atom, but each has one equal-rank wing in the complementary
`J_u=+1` sector.  The crossed-zero row sees no commutator on that wing and
does not return it to the parent atom.

Thus taking depth `N>log_2 d` gives no operator-norm gap: here `d=12`, all
local exactification errors are zero, and the model exists for arbitrary
`N`.  Local parent/range exactification plus lossless conjugacy cannot force
a useful coherent character collision.  A load-bearing prototype must test
the **holonomy between two distinct address words with the same three-state
value**, or couple cousin coefficient arms so that their complementary
wings cannot be reused.

This does not refute the unrestricted three-row atomic compiler.  It rules
out the coordinate-adaptive full-prefix strategy when its fixed menu
contains only the local inverse, range-sum, one-arm Whitehead, and attached
reverse-range crossed-zero cells.

No Property `(T)`, Kazhdan input, stability theorem, or literature result is
used.

DERIVATION
full-prefix-three-state-model-proof
