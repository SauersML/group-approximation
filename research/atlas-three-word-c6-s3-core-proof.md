---
rg: 2
id: atlas-three-word-c6-s3-core-proof
kind: route
title: Read the two packet pairs and collision into order-six subgroup coordinates
target: atlas-three-word-c6-s3-core
requires:
  - atlas-a4-two-context-collision-gap
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_three_word_permutation_countermodel.py
  - experiments/atlas-word-19243.json
---

Use the exact `F_2^4` matrices in the two-context packet and collision file.
Write

```text
a = 01010000010000000000010000000001,
b = 01000000010100000000010000000001,
c = 01000000000100000000010100000001.
```

Direct multiplication over `F_2` gives

```text
a^3=b^2=c^2=1,
[a,c]=1,
|<a,c>|=6,
|<a,b>|=6.
```

The first group is therefore `C3 x C2 = C6`.  The second has an element of
order three and an involution with `bab=a^-1`, hence is `S3`.

The second packet context has exactly

```text
b_v = b a,
a_v = a^2.
```

The four factor-two syllables of collision 19243 are, in order,

```text
a, b, a^2, b a,
```

while every factor-one syllable of that collision is `c`.  Thus after naming
the factor-two images `x=a`, `y=b`, `z=ba=yx`, the three words are precisely

```text
(y r)^3,
(z r^-1)^3,
x c y c x^-1 c z c,
```

with `r` the factor-one copy of `a`.

Finally, restriction of the regular representation of a finite group to a
subgroup is one regular representation of the subgroup for each left coset.
Both subgroups have order `6`, so

```text
Res Reg(A8) = 3360 Reg(C6)
Res Reg(A8) = 3360 Reg(S3).
```

This proves the stated core for the original multiplicities.  Amplifying any
`m`-copy core by `3360` preserves normalized-HS defects and lands at original
multiplicity `k=m`, while every original instance is already a core instance.
Hence the two infima are equal.

The companion experiment performs all displayed finite-field identities using
integer arithmetic, independently of any floating-point optimization.
