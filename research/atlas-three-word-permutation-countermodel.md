---
rg: 2
id: atlas-three-word-permutation-countermodel
kind: claim
title: The proposed three-word A4 amplified gap has an exact 12-point permutation countermodel
invalidates: [atlas-a4-three-word-amplified-gap]
artifacts:
  - experiments/atlas_three_word_permutation_countermodel.py
---

The fixed three-word packet consisting of tree words `6910`, `6940`, and
collision `19243` has **zero** energy in an exact finite permutation model,
and the model amplifies to every regular-`A8` multiplicity used by the atlas
criterion.  Consequently there is no positive constant `epsilon` satisfying
`(A4-3W-GAP)`.

More precisely, after the exact support reduction encoded in the artifact,
the first-chart letters seen by the three words generate `C6`, while the
second-chart letters generate `S3`.  On twelve points take two regular
`C6`-orbits, with

```text
r = translation by 2 on each orbit,
c = translation by 3 on each orbit.
```

There are fixed-point-free involutions `y,z` for which, with `x=yz`,

```text
x^3=1,
(yr)^3=1,
(zr^-1)^3=1,
x c y c x^-1 c z c=1,
```

and `<x,y>` has two regular `S3`-orbits.  Thus the two pair-cubes and the
collision word all evaluate exactly to the identity while both subgroup
margins have the required regular type.

Repeating the twelve-point core `1680*k` times gives dimension `20160*k`, so
the countermodel lies in precisely the amplification sector quantified by
`atlas-a4-three-word-amplified-gap` for every `k>=1`.

This no-go is specific to the three selected words.  It does not affect the
thirty-context A4 coherence/ellipse lane, whose additional contexts are what
must kill this nonclassical local solution.
