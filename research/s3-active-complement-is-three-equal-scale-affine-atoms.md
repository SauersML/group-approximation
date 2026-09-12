---
rg: 2
id: s3-active-complement-is-three-equal-scale-affine-atoms
kind: claim
title: The S3 active complement is three affine atoms at one common spin scale
distinct_from:
  packet-central-active-complement-reduces-shared-words: that proves the union approximately reduces shared words; this resolves its internal finite-packet scale and decomposes it into three separately transportable affine atoms.
  q-masa-selector-bridge-is-scale-conservation: that finds an inverse spin/multiplicity trade across a generic q-MASA bridge; here every active atom and the one-jump exit have exactly the same spin dimension.
artifacts:
  - experiments/s3_equal_scale_active_atoms.py
  - experiments/s3-equal-scale-active-atoms.json
---

Use the six-generator packet of
`six-generator-one-jump-router-has-s3-radical-atlas`, fix any nonzero radical
endpoint word `b` from `(SRA6)`, and put

```text
Q=(1-J)/2,        F=(1-K)/2,        B=(1-b)/2,
P_(epsilon,delta)=Q (1+epsilon K)/2 (1+delta b)/2.       (SEA1)
```

Then

```text
A=Q-QFB=P_(+,+)+P_(+,-)+P_(-,+),
X=QFB=P_(-,-).                                           (SEA2)
```

The four projections in `(SEA1)` are pairwise orthogonal.  In every exact
finite-dimensional representation of the packet, each of their ranks is a
multiple of four, and on the `K=-1,J=-1` sector one has the stronger equality

```text
rank P_(-,+)=rank P_(-,-).                               (SEA3)
```

Equivalently, after measuring Hilbert dimension in units of the common
four-dimensional spin packet, the active complement is the three-coordinate
integer vector

```text
(n_(+,+),n_(+,-),n_(-,+)),                               (SEA4)
```

while the one-jump exit has multiplicity exactly `n_(-,+)`.  Tensoring with
any fixed Schur baseline packet multiplies the common unit by its fixed spin
dimension and leaves `(SEA2)--(SEA4)` unchanged.

Thus the nonlinear union in `(SEA2)` creates no local Morita-scale problem.
It may be transported as three ordinary affine character coordinates.  The
remaining return problem is coherence/holonomy among their external
multiplicity spaces, not conversion of `A` into one scalar group word.

The replayable form audit checks all three endpoint words.  Each is radical
in the rank-four form and has explicit anticommuting basis partners in the
rank-six form, confirming the `4 -> 8 -> 4+4` scale calculation.
