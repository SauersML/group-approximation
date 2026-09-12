---
rg: 2
id: iwahori-outlier-repair
kind: claim
title: "Iwahori endpoint: full-rank outlier repair"
artifacts:
  - research/artifacts/open-problem-attacks-2026-08-17.md
  - research/artifacts/psl2-far-sector-optimizer-heuristic-2026-08-21.md
  - research/artifacts/user-reported-augmented-lagrangian-hnn-probe-2026-08-21.md
  - experiments/psl2_far_sector_probe.py
  - experiments/psl2-far-sector-probe-smoke.json
  - notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md
  - notes/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md
  - notes/FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md
---

In the only unresolved Dogon–Vigdorovich sector: an `o(d_n²)` low-energy
operator space contains a matrix near the full-rank identity; use its origin
from two exact modular vertex representations to turn it into an exact
invertible edge intertwiner after only `o(d_n)` padding
(HIGHEST_YIELD 2026-08-14). Spectral sparsity alone is insufficient — even
the scalar line contains invertible matrices.

**Dependency audit after congruence closure (2026-08-23).**  Here “modular
vertex” means `SL_2(Z)`, not a modular finite quotient.  Localization does
not make either vertex representation congruence.  Indeed
`modular-vertex-extension-does-not-force-congruence` gives arbitrarily
high-dimensional infinite-image edge irreducibles extending through a
modular vertex.  Thus the mixed-CRT and odd-label repair theorems close every
pair already in the congruence locus but do not close this endpoint.  The
sharp sufficient preprocessing statement is now
`regular-iwahori-relative-congruence-exactification`; if it holds, the route
`relative-congruence-exactification-closes-outlier` applies uniform exact
congruence repair.  Canonical trace and property `(tau)` do not themselves
supply that preprocessing.

## Attempts

**2026-08-17, external pass (`research/artifacts/open-problem-attacks-2026-08-17.md`,
section 1).**  The sector was re-attacked from the two levers the repository
already owns, and both were checked and found insufficient.  Recorded so the
next session does not spend the same day.

- *Spectral sparsity.*  Confirmed insufficient, for the reason this node
  already states: an `o(d_n^2)` operator subspace can contain a full-rank
  invertible matrix — the scalar line is the example — so localization
  (`notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md`) cannot by
  itself bound the rank of the repair.
- *Bounded branching.*  This is the new negative datum.  Index-three
  restriction/induction has uniformly bounded branching
  (`notes/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md`), and that does
  **not** prevent the identity's mass from spreading over a growing number of
  cross-pairs of edge constituents.  So bounded branching does not convert the
  sparse low-energy outlier into `o(d_n)` removable padding.
- *What was looked for and not found.*  A uniform transversality theorem for
  the two opposite modular extension loci.  Nothing in the repository supplies
  one, and no substitute argument turned up.

The obstruction is therefore physical rank, not Hilbert-space dimension, and
it is still unaddressed.  The live reduction it blocks is unchanged in
substance, with one intermediate now named explicitly (2026-08-19):
`edge-pair-mixed-gap-collapse` -> `iwahori-outlier-localization` -> this claim
-> `iwahori-defect-question-from-outlier-repair`
-> `iwahori-local-global-defect-question` -> `iwahori-sector-closure`
-> `non-hyperlinear-group`.  That intermediate is Dogon--Vigdorovich's printed
Question 1.2; this claim is a sufficient condition for it in the one sector
their variety decomposition leaves open.

- *Bounded adversarial probe, 2026-08-21.*
  `experiments/psl2_far_sector_probe.py` now exposes small CLI budgets and was
  smoke-tested on MSI at `d=6` with one restart and `120` steps.  Rewarding
  short-odd-order farness did not lower the gluing defect (`.574` versus
  `.520` without the reward), but this is only a development check.  The
  diagnostic scans odd orders only up to a chosen cutoff and is explicitly
  not a certificate of distance from the full congruence locus.


- **Skeleton reframing bypasses the physical-rank obstruction
  (2026-08-21).**  The obstruction recorded above is that a sparse
  low-energy outlier must be repaired to an exact FULL-RANK edge
  intertwiner, and no two-loci transversality theorem supplies it.
  The route through `skeleton-relative-hs-stability-for-sl2` avoids
  repairing an outlier at all: Levit--Vigdorovich stability of
  `BS(1,4)` plus the proved
  `bs14-exact-representation-variety-is-hs-locally-rigid` make BOTH
  parabolic towers EXACT with finite odd order before the edge is
  touched, and then the Weyl element is not an outlier to be
  rank-repaired but is imposed EXACTLY by DEFINING the lower tower as
  its swap image (`L(y) := s pi_+(-y) s^{-1}`).  So the full-rank
  object is the exact swap `s`, needing no `o(d)` padding, and the
  only approximate data left is the pair of scalar-type holonomies
  `(R1), (R2)` living in the compact centralizer torsor -- not in the
  rank.  This also dissolves the missing transversality-of-two-loci
  theorem: there are not two independent extension loci to make
  transverse, but ONE exact tower and a fixed involution (the swap)
  acting on it, whose self-consistency is `(R1)` and whose second
  Weyl relation is `(R2)`, and the two collapse to one by the
  Steinberg cocycle syzygy `w(s)w(t)^{-1}=h(s/t)`.  The remaining
  content is torsor absorption, not rank repair -- a different and
  more tractable shape for the same edge.
