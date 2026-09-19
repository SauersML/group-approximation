---
rg: 2
id: atlas-a5-large-rectangle-cannot-share-marked-collision-seam
kind: claim
title: The A5 large-rectangle completion is incompatible with the marked S3-square/S4 collision seam
artifacts:
  - experiments/atlas_a4_a5_atlas_nondevelopable.py
  - research/artifacts/atlas-a4-a5-atlas-nondevelopable.json
distinct_from:
  atlas-full-large-rectangle-is-balanced-s720-two-cycle: that proves equality of all regular edge multiplicities; this proves that its selected A5 local completion has inconsistent transported intersections and hence cannot be glued faithfully.
  atlas-large-k22-has-faithful-a5-completion: that proves A5 is faithful on the isolated large rectangle; this proves that the same completion cannot coexist with the noncentral collision S4 and first S3-square packet.
  atlas-full-large-no-simple-quotient-under-million: that excludes finite simple targets by exhaustive computation; this is an exact three-vertex nondevelopability proof with no target-order bound.
---

Let the selected full-large rectangle vertex be the marked `A5` from
`atlas-large-k22-has-faithful-a5-completion`.  Its two radial `S3` subgroups
have the nontrivial intersection

```text
d = r^-1 u r = t^-1 s t,             |<d>|=2.          (A5-SEAM-1)
```

In the first packet `F=<r,z,c,u> ~= S3 x S3`, the collision involution `c`
commutes with both `r` and `u`.  It therefore commutes with `d`:

```text
[c,d]=1 in F.                                             (A5-SEAM-2)
```

This transported relation is incompatible with the marked collision vertex
`J=<t,s,c> ~= S4`.  In the exact collision-19243 calibration,
`d=t^-1 s t` is a transposition, `c` is a double transposition, and

```text
|<c,d>|=8,
[c,d] != 1,
|<<[c,d]>>_J|=4,
c in <<[c,d]>>_J.                                      (A5-SEAM-3)
```

Thus the normal closure in `J` of the relation forced by `F` is its normal
Klein four.  Imposing `(A5-SEAM-2)` kills `c` and collapses `J` to its `S3`
quotient.  There is no group receiving the marked maps from `F`, `A5`, and
`J` injectively with their prescribed overlaps.  In particular the balanced
`S720` A5-based finite-vertex atlas is nondevelopable before its `C144`
vertex is attached.

This conclusion is specific to the selected A5 completion.  The four
large-rectangle relators have other faithful finite local completions (the
bounded census includes orders `168` and `1920`), so this does not by itself
collapse the universal full-large presentation.
