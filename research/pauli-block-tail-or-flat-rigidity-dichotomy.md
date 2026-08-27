---
rg: 2
id: pauli-block-tail-or-flat-rigidity-dichotomy
kind: claim
title: Each Pauli comb block is either spiky enough to branch or flat enough to force common-block coherence
artifacts:
  - notes/TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md
  - notes/TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md
  - notes/TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md
  - research/artifacts/fractional-branch-pressure-2026-08-19.md
distinct_from:
  atlas-a4-holonomy-coherence-gap: that is a numerical ceiling on the two S3 covariance defects of exact regular A4 context networks; this is a dichotomy on the singular-value distribution of the sixteen raw-to-comb blocks and its two branches end in different obstructions.
  constant-block-contraction-gap: that is the unconditional block inequality plus its consequence under a coherence hypothesis; this is the missing statement that the coherence hypothesis holds whenever the blocks are not spiky.
  atlas-supercritical-pauli-branching-cycle: that asks directly for a supercritical integer cycle; this asks for a case analysis whose spiky branch supplies fractional coverage and whose flat branch supplies rigidity instead.
---

Work in the fixed two-qubit raw/comb Pauli packet, with the comb compression
written as a contraction `T=(T_ij) in M_4(N)` whose sixteen blocks have exact
mass `||T_ij||_(2,N)^2 = 1/8`, as established in
`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md`.

There exist fixed constants `t in (0,1)`, `theta>0`, `C>0`, `c>0`, independent
of matrix dimension, such that in every atlas microstate of relator defect
`delta` at least one of the following holds.

**(TAIL)** Some source state has thresholded coverage above the critical line:
there is a state `P_i` in the finite family with

```text
sum_j c_(ij)(t) > 1,
```

for the coverage `c(t)` of `soft-block-mass-yields-fractional-branch`, with
leakage and ordered-pair Gram energy `O(delta^c)`.

**(FLAT)** The sixteen blocks are jointly `theta`-flat, and after the fixed
Pauli phase untwist there is `C_delta in N` with

```text
(1/4) sum_(i,j) ||T_ij - C_delta/2||_(2,N)^2 <= C delta^c.
```

In case `(TAIL)`, `fractional-source-branch-pressure` applies and the microstate
sequence is contradicted through
`atlas-fractional-pauli-return-network`.  In case `(FLAT)`, `(CBG5)` of
`constant-block-contraction-gap` gives the fixed floor `3/4 - 1/sqrt(2)` and the
microstate sequence is contradicted directly.  So the dichotomy plus either
endpoint closes the packet.

## Why the dichotomy is the right shape

`supercritical-network-needs-noncanonical-cuts` shows that the flat character
data is subcritical by a factor of two and could not have been otherwise, since
those masses are canonical.  So flatness is exactly the configuration in which
branch pressure is unavailable.  The content of the dichotomy is that flatness
is not free either: sixteen simultaneously flat blocks of a contraction are a
very rigid object, and rigidity is what `constant-block-contraction-gap`
punishes.  Neither escape is closed by the other, which is why the singular
value distribution, rather than the block mass, is the correct object.

## Attempts

- **The real gap is flat-to-common, not flat-to-isometric.**  Joint
  `theta`-flatness gives sixteen blocks each close to a scaled partial isometry.
  It does **not** give one *common* coefficient `C_delta`.  Recovering the
  common block is exactly the Reynolds step of
  `TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md` section 5, and section 7
  states it as four bounded finite-coordinate row/column shifts with vanishing
  phase-corrected defect.  This node is open precisely on that step.
- **The shifts cannot be group words.**  Section 6 of the same note proves it:
  literal word-implemented translations would force the same conclusion in the
  regular representation, where the trace-flat packet exists and `(CBG2)` also
  holds.  So do not search for four translation words; the shifts must come
  from equal-rank matrix units, matching `(NCC2)` of
  `supercritical-network-needs-noncanonical-cuts`.
- **Calibrating `theta` against `t`.**  The two branches must exhaust the
  possibilities, so the flatness threshold `theta` has to be chosen from the
  same `t` that defines the coverage in `(TAIL)`.  A block failing `(TAIL)` has
  its spectral mass concentrated below `t`, and `(SBM2)` bounds how much mass
  can sit above `t`; turning that two-sided pinch into joint flatness with a
  usable constant is unattempted arithmetic, not a research obstacle, but it
  has not been done.
- **Do not weaken `(TAIL)` to per-block spikiness.**  A single spiky block is
  useless: `(NCC3)` shows four blocks out of one raw cut total at most `1/2` on
  the flat table, so `(TAIL)` must be a statement about the *sum* over targets,
  and it can only be met by refining the states below the character cuts.
