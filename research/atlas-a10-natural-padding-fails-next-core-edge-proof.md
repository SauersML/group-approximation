---
rg: 2
id: atlas-a10-natural-padding-fails-next-core-edge-proof
kind: route
title: Transporter enumeration and fixed-orbit proof for the padded A10 carrier
target: atlas-a10-natural-padding-fails-next-core-edge
requires:
  - atlas-forward-collision-has-faithful-a10-quotient
artifacts:
  - experiments/atlas_a4_a10_first_chart_extension.g
  - experiments/atlas_a4_a10_next_core_overgroup.g
  - research/artifacts/atlas-a4-a10-next-core-natural-padding.json
---

The first script constructs the natural `A8` as the pointwise stabilizer of
points `1,8` in the certified `A10`, computes an isomorphism from the canonical
`GL4(2)` chart, and enumerates the normalizer transporter which fixes the
ordered tuple `(r,z,c)`.  It contains twelve elements.  Evaluating the four
large-component pair-cubes on each gives the single mask `0x1`, twelve times.

The second script does not assume an `A8` extension.  In `S_d` it computes the
transporter inside `C_Sd(<z,c>)` from `r` to `r^-1`, filters for involutions,
and tests `(u t^-1)^3`.  The exact calibration for `10<=d<=16` is stored in
the artifact; the next-edge count is zero in every degree.

For all degrees, the relations imply `u F u=F`.  A normalizer permutes the
orbits of an action preserving their sizes and stabilizer type, so the unique
nontrivial eight-point orbit is preserved and its complement `T` is
preserved.  Since `t|_T=1`, restriction of `(u t^-1)^3=1` gives `u^3|_T=1`.
But `u^2=1`, hence `u|_T=1`.  Removing `T-{1,8}` produces a degree-ten
solution, contradicting the exact degree-ten transporter calculation.
