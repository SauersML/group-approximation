---
rg: 2
id: iwahori-outlier-repair
kind: claim
title: "Iwahori endpoint: full-rank outlier repair"
artifacts:
  - research/artifacts/open-problem-attacks-2026-08-17.md
  - docs/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md
  - docs/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md
  - docs/FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md
---

In the only unresolved Dogon–Vigdorovich sector: an `o(d_n²)` low-energy
operator space contains a matrix near the full-rank identity; use its origin
from two exact modular vertex representations to turn it into an exact
invertible edge intertwiner after only `o(d_n)` padding
(HIGHEST_YIELD 2026-08-14). Spectral sparsity alone is insufficient — even
the scalar line contains invertible matrices.

## Attempts

**2026-08-17, external pass (`research/artifacts/open-problem-attacks-2026-08-17.md`,
section 1).**  The sector was re-attacked from the two levers the repository
already owns, and both were checked and found insufficient.  Recorded so the
next session does not spend the same day.

- *Spectral sparsity.*  Confirmed insufficient, for the reason this node
  already states: an `o(d_n^2)` operator subspace can contain a full-rank
  invertible matrix — the scalar line is the example — so localization
  (`docs/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md`) cannot by
  itself bound the rank of the repair.
- *Bounded branching.*  This is the new negative datum.  Index-three
  restriction/induction has uniformly bounded branching
  (`docs/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md`), and that does
  **not** prevent the identity's mass from spreading over a growing number of
  cross-pairs of edge constituents.  So bounded branching does not convert the
  sparse low-energy outlier into `o(d_n)` removable padding.
- *What was looked for and not found.*  A uniform transversality theorem for
  the two opposite modular extension loci.  Nothing in the repository supplies
  one, and no substitute argument turned up.

The obstruction is therefore physical rank, not Hilbert-space dimension, and
it is still unaddressed.  The live reduction it blocks is unchanged:
`edge-pair-mixed-gap-collapse` -> `iwahori-outlier-localization` -> this claim
-> `iwahori-sector-closure` -> `non-hyperlinear-group`.
