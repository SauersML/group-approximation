---
rg: 2
id: atlas-l44-subfield-packet-collision-exclusion
kind: claim
title: The augmented Atlas packet excludes the L4(4) subfield A8 equality case
artifacts:
  - experiments/atlas_a4_l44_fan_escape.py
  - experiments/atlas_a4_l44_bitpacked_screen.py
  - experiments/atlas-a4-l44-bitpacked-screen.json
distinct_from:
  atlas-l44-local-packet-fans-do-not-force-subfield-support: that proves the local fan and H6-only shortcuts fail; this asks for the common-frame coupling of both packet components and collision.
---

For the standard subfield chart `A=GL4(2)<L4(4)`, no marked conjugate chart
`B` satisfies all twelve distinct packet edges together with collision
`19243`.  This holds for both relative marking parities: an inner marking and
the graph-outer marking `g -> (g^-1)^T`.

In either parity there are `1262` ordered `H6` rectangle pairs, and,
surprisingly, every one has an invertible common intertwiner.  Their
projective `H6` centralizer fibers have size `180`, hence give `227160`
structured common-frame candidates.  The `H18` edges leave `2754` full-packet
survivors (`30` projectively binary frames and `2724` extension frames).
Collision `19243` kills all of them; before imposing it, its values have exact
order histogram

```text
order 2: 1863,    order 4: 891.                       (L44S1)
```

The q14 relation alone leaves `729` survivors in inner parity and `486` in
graph parity, but none also satisfies collision `19243`.

## Earlier failed reductions

- One-vertex support recognition fails exactly: the two fan fibers have `336`
  and `150` points, with nonsubfield points in both.
- The first proposed prefilter is provably blind:
  `atlas-l44-h6-spectrum-is-blind-on-all-rectangle-pairs` shows all `1262`
  pairs have the source order-three characteristic polynomial.  The exact
  screen therefore retains simultaneous nonsemisimple `S3` data instead of a
  scalar spectral shortcut.
