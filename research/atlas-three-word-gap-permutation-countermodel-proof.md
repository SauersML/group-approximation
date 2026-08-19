---
rg: 2
id: atlas-three-word-gap-permutation-countermodel-proof
kind: route
title: Twelve-point permutation arithmetic gives zero three-word energy at every A8 multiplicity
target: atlas-three-word-gap-permutation-countermodel
requires:
  - atlas-three-word-c6-s3-core
artifacts:
  - experiments/atlas_three_word_permutation_countermodel.py
---

Use the permutations displayed in the target claim.  The fixed pair `r,c`
consists of two regular `C6` orbits.  The second pair `x,y` satisfies

```text
x^3=y^2=1,
y x y=x^-1,
```

and its orbit decomposition is

```text
{0,1,3,4,6,9},
{2,5,7,8,10,11}.
```

Both orbits have size `|S3|=6`; hence this is exactly `2 Reg(S3)`.  Put
`z=yx`.  Direct composition gives

```text
(y r)^3=1,
(z r^-1)^3=1,
x c y c x^-1 c z c=1.
```

These are exactly the three atlas words by
`atlas-three-word-c6-s3-core`.  Therefore the core energy at multiplicity two
is zero.  Direct-summing `1680 k` copies gives core multiplicity `3360 k` and
dimension `20160 k`, with the normalized defects still exactly zero.  The core
reduction then supplies a relative unitary for the two regular A8 charts at
each original multiplicity `k`.

The experiment independently enumerates all fixed-point-free candidate
involutions satisfying the two pair-cubes.  There are `162` candidates for
each side and exactly `72` regular-S3 pairs satisfying collision 19243 as
well; the listed witness is the first one.  The enumeration is not needed for
existence once the displayed permutations are checked, but guards the finite
certificate against transcription errors.

Thus no `epsilon>0` can satisfy `A4-3W-GAP`.
