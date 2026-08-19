---
rg: 2
id: atlas-three-word-gap-permutation-countermodel
kind: claim
title: The proposed three-word amplified atlas gap has an exact 12-point permutation countermodel
invalidates:
  - nonhyperlinear-from-three-word-atlas-gap
artifacts:
  - experiments/atlas_three_word_permutation_countermodel.py
distinct_from:
  atlas-a4-three-moment-classical-separator: that separator is correct on the finite alphabet of A8 automorphism alignments; this countermodel uses a regular S3 placement which does not extend to one of those chart automorphisms.
---

The positive-gap target `atlas-a4-three-word-amplified-gap` is false.  Already
at multiplicity `m=2` in the exact `C6`--`S3` core there are permutation
representations for which all three candidate words are the identity.

On twelve points take

```text
r = (0 2 4)(1 3 5)(6 8 10)(7 9 11),
c = (0 3)(1 4)(2 5)(6 9)(7 10)(8 11),
```

so `<r,c>` is `2 Reg(C6)`.  Take

```text
x = (0 1 9)(2 8 7)(3 4 6)(5 11 10),
y = (0 3)(1 6)(2 10)(4 9)(5 7)(8 11),
z = (0 6)(1 4)(2 11)(3 9)(5 8)(7 10).
```

Then `z=yx`, `<x,y>` has two orbits of size six and is therefore
`2 Reg(S3)`, and direct permutation multiplication gives

```text
(y r)^3 = 1,
(z r^-1)^3 = 1,
x c y c x^-1 c z c = 1.                              (EXACT-3W)
```

Repeating this twelve-point core `1680 k` times gives multiplicity
`m=3360 k`, exactly the restriction multiplicity of `Reg(A8) tensor I_k` to
either order-six support subgroup.  By `atlas-three-word-c6-s3-core`, the
resulting regular-`A8` relative unitary has zero defect on `u,v,q` for every
`k>=1`.

Thus the infimum in the proposed amplified gap is exactly zero, not merely
small.  Any atlas obstruction must use more information than these two A4
pair-cubes and collision 19243.
