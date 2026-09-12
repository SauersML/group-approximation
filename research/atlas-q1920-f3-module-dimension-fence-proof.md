---
rg: 2
id: atlas-q1920-f3-module-dimension-fence-proof
kind: route
title: Enumerate faithful modular Q1920 packets with radial fixed vectors
target: atlas-q1920-clifford-four-dimensional-shortcut-fails
requires:
  - atlas-q1920-is-radial-holonomy-extension
artifacts:
  - experiments/atlas_a4_q1920_f3_module_fixed_spaces.g
  - experiments/verify_atlas_q1920_finite_certificates.py
  - research/artifacts/atlas-a4-q1920-f3-module-fixed-spaces.json
---

The verifier reconstructs the two marked order-1920 images from the complete
degree-at-most-twelve local census.  For each image it enumerates all
irreducible `F3[Q]` modules, computes the order of the matrix image, and row
reduces the simultaneous fixed-space equations for the two radial `S3`
subgroups.

After retaining faithful images and a nonzero fixed space for the first
radial subgroup, the exact profiles for either marking are

```text
(dimension,A-fixed,B-fixed)
  (6,2,0), (10,3,1), (10,1,3), (24,4,4).
```

For the other marking the two faithful six-dimensional orientations are
interchanged; the same four retained profiles result.  Thus the marked
local data really do admit irreducible packets of dimensions `6,10,24`
carrying a candidate fixed vector.  Since the complement `A5` is not normal
in a putative ambient action, irreducibility of that ambient chief factor
does not identify it with the four-dimensional `A5`-cyclic span.  This is
exactly the claimed failure of the dimension-four shortcut; it does not
assert that any of these local packets extends to a full seam completion.

The independent audit checks both twelve-row module inventories, image
orders, the radial swap, and the source/output checksums.
