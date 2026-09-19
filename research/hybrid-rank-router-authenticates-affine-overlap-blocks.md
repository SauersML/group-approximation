---
rg: 2
id: hybrid-rank-router-authenticates-affine-overlap-blocks
kind: claim
title: A finite role packet authenticates the two affine hybrid blocks for rank conjugacy
refuted_by: hybrid-rank-router-tensor-closure-obstruction
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
  - research/artifacts/hybrid-rank-router-tensor-closure-2026-08-23.md
distinct_from:
  common-partial-isometry-swap-game-compiler: that selects a nonlinear BCS predicate on one common D8 Gram; this routes only A, B, AB, and 1 after independent-set normalization and needs no common Gram.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that rules out universal nonlinear truth-table selection; the proposed packet performs affine block placement while rank conservation supplies the nonlinearity.
  two-letter-dihedral-swap-wordizes-one-gram-row: that reads one desired off-diagonal intertwining block but does not assemble both two-copy hybrids required here.
  source-specific-pointed-rank-router-face: that is the surviving non-tensor-closed, one-source replacement after the universal exact-extension statement here is refuted.
---

**REFUTED AS STATED.**  The requested universal router cannot exist by
`hybrid-rank-router-tensor-closure-obstruction`.  The original target was to
construct one fixed finite ordinary-group role packet with a
robust two-copy decoding operation having the following property.  Given two
flexible involution words

```text
A=1-2P,                  B=1-2Q,
```

from the row-clock PVMs, fixed role words decode unitaries `R,S` satisfying

```text
R=diag(A,B),             S=diag(AB,1)                 (HRR1)
```

on two equal authenticated blocks.  In approximate finite-dimensional
representations, the squared Hilbert--Schmidt distance from `(HRR1)` is
bounded by a dimension-independent constant times the fixed routing-relator
energy.

For every forbidden pair the presentation may adjoin a stable letter `U_f`
and the ordinary relation

```text
U_fR_fU_f^*S_f^*=1.                                   (HRR2)
```

The packet was required to have exact tracial extension: whenever `PQ=0`, the unitary
from `rank-conjugacy-detects-projection-overlap` can be chosen as `U_f`, so
all routing and conjugacy relators vanish without killing the marked corner.

Only the four already available words `A,B,AB,1` were to be routed.  No selected
NAND irrep, common Gram carrier, outcome-multiplicity profile, or
cross-context alignment may be assumed.  A finite nested D8 role tree is one
candidate because `two-letter-dihedral-swap-wordizes-one-gram-row` tolerates
an uncontrolled complementary block, but no existing claim assembles both
hybrids in `(HRR1)`.

The failure is categorical, not a missing D8 identity.  Exact ordinary-group
representations are tensor closed, whereas the admissible scalar relation
`PQ=0` is not tensor closed under multiplication of the reflection words.
Three exact admissible extensions in the negative marked sector tensor to an
exact representation with `A=B=-1`.  Universal routing would then give
`R=-I` and `S=I`, contradicting the still-exact conjugacy relator `(HRR2)`.

The surviving endpoint is
`source-specific-pointed-rank-router-face`: retain only one distinguished
perfect tracial source and prove routing for the non-tensor-closed pointed
trace face containing canonical microstates.  In particular, a viable
compiler cannot promise exact extension for every abstract zero-overlap pair.
