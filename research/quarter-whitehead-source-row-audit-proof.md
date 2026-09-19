---
rg: 2
id: quarter-whitehead-source-row-audit-proof
kind: route
title: Audit the named Pauli, Hecke, and compression covariance rows against the quarter Whiteheads
target: quarter-whiteheads-lack-unequal-source-conjugacy
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
  - center-chain-four-hecke-flags-have-native-ranks
  - hecke-quarter-selector-is-untyped-or-rank-preserving
  - native-whitehead-corner-collapses-hecke-flags
  - compression-preimage-whitehead-preserves-gauge
  - projective-row-data-do-not-authenticate-hecke-polars
---

For `q=1/4`, formula `(TSG1)` is

```text
Phi_(1/4)(theta)=3/4-theta/2.
```

Substitution of source fractions `1/2` and `1/4` proves `(QWS3)`.  The
robust estimate `(TSG3)` gives the first two inequalities in `(QWS4)`;
the triangle inequality on the two forced values `1/2,1` gives the sum and
maximum bounds.  Minimizing the sum of squares at `theta=3/4` gives `1/8`.

Equations `(SCWP2)--(SCWP3)` are exactly `(QWS5)`.  In the tensor form
`W_m=SWAP tensor V_m`, conjugation of a Pauli operator `P tensor 1`
contains `V_m` once on each side, so its two copies cancel.  These rows
therefore cannot place `V_m` in the target reflection.

Equations `(FHF2)--(FHF3)` give the four Hecke support ranks but no
conjugacy.  They are projections in a Hecke group-algebra corner; converting
them to `1-2r_i` is analytic syntax, not an ordinary group word.  The
regular/coset dichotomy `(HCQ1)--(HCQ4)` proves that the quarter rank is not
a representation-independent ordinary involution type.  On a common
reducing Whitehead corner, `(CNW9)` is precisely
`(QWS6)`, while `(CNW11)` retains both quarter-label swaps.  Thus neither
the full Hecke carrier nor its common Whitehead reduction supplies
`(QWS2)`.  Finally `(CPW3)--(CPW4)` give `(QWS7)` and its two-chart gauge
equation, which has no fixed unequal source-rank assertion.

For the finite fence, adjacent transpositions in `S_3` are involutions,
satisfy the braid, and are conjugate.  Tensoring them onto the canonical
three-qubit swap model verifies every same-center row.  The independent
balanced spectator construction preserves all separately projective native
rows and their ranks.  Since the audited menu contains no mixed equality
between those target names and `W_i`, the direct product verifies their
union and leaves the missing identification free.
