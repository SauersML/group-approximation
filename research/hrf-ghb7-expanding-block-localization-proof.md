---
rg: 2
id: hrf-ghb7-expanding-block-localization-proof
kind: route
title: Fix the failure scale, decompose by Liu, discard relator-bad blocks, and assemble flexible roundings by dimension weights
target: hrf-ghb7-expanding-block-localization
requires:
  - quotient-gap-gives-large-scalar-expanding-blocks
artifacts:
  - research/artifacts/hyperbolic-rf-ghb7-2026-09-20.md
---

The complete proof is in Sections 1-4 of the artifact. Property (T)
supplies the quotient conjugation gap for an asymptotic representation.
If its rounding cost is >=eta, choose epsilon and gamma with
gamma+2 sqrt(epsilon)<eta before applying the prerequisite. It gives
one fixed scalar gap c and doubled block tuples with vanishing weighted
relator defect. Uniform rounding of fixed-c tuples, which is equivalent
to sequential rounding by contraposition, rounds every relator-good
block. Markov bounds the physical trace of bad blocks by A_n/delta^2.
Fill those blocks and the discarded block trivially, then direct-sum
the good roundings. Dimension inflation is <=gamma and generator error
has ultralimit <=gamma+2 sqrt(epsilon), contradiction. The reverse
implication is restriction of stability to these tuples. Failure of
the resulting criterion selects a fixed-c sequence; compactness in
each bounded dimension forces its dimensions to tend to infinity.

Liu's analytic block theorem remains an explicit prerequisite. This
route neither reproves it nor silently replaces its doubled generators
by single copies.
