---
rg: 2
id: full-whitehead-clifford-hyperlinearity-equivalence-proof
kind: route
title: Apply finite-edge hyperlinearity permanence and evaluate the odd-row floor in the regular representation
target: whitehead-clifford-graft-hyperlinear-iff-base
requires:
  - full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark
  - amenable-edge-graph-corners-cannot-groupify-a-nonce-game
  - odd-row-unoriented-fine-return-has-quarter-floor
---

Bass--Serre normal form embeds the affine-Leavitt vertex group in the cyclic
amalgam, giving the forward implication of `(HCE2)` by subgroup permanence.
For the converse, the other vertex is finite and the edge is `C_4`, so the
amenable-edge amalgamation theorem applies.

In the left regular representation of the amalgam, the restriction to the
finite packet is its regular representation.  Hence the primitive type and
signed source/target projections have the traces in `(HCE4)`.  All group
relations are exact, so the odd-row defect in the established quarter-floor
inequality is zero.  The remaining support leakage is therefore at least
`1/16`, proving `(HCE6)` and the tracial firewall.

For a canonical matrix microstate sequence, the leakage square is the trace
of a fixed `*`-polynomial and therefore converges to this regular value.  It
cannot tend to zero.  Conversely, in the absence of canonical microstates
the universal asymptotic support assertion is vacuous.  This proves
`(HCE8)--(HCE9)`.
