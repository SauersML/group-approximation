---
rg: 2
id: atlas-three-word-a5xc2-countermodel
kind: claim
title: A5 times C2 gives an algebraic twelve-point escape from the three-word atlas test
artifacts:
  - experiments/atlas_three_word_permutation_countermodel.py
distinct_from:
  atlas-three-word-gap-permutation-countermodel: that gives an exhaustive twelve-point permutation certificate; this identifies a closed-form finite-group mechanism producing such a certificate without search.
---

The zero-energy escape behind `atlas-three-word-gap-permutation-countermodel`
comes from the finite group

```text
G = A5 x C2.
```

In `A5` take

```text
r = (1 2 3),
x = (3 4 5),
y = (1 2)(3 5),
z = (1 2)(3 4).
```

Then

```text
z = yx = x y x^-1,
(yr)^3 = 1,
(z r^-1)^3 = 1.
```

Let `c` be the central generator of the `C2` factor.  Since `c` is central,

```text
x c y c x^-1 c z c = x y x^-1 z = z^2 = 1.
```

There is moreover a twelve-point transitive permutation representation of `G`
whose restrictions to `<r,c> ~= C6` and `<x,y> ~= S3` are both exactly two
copies of their regular representations.  Hence this finite group already
supplies the `m=2` core of `atlas-three-word-c6-s3-core`; no numerical or
continuous-unitary phenomenon is involved.

Concretely, let `D10=<d,s><A5` with

```text
d=(1 2 3 4 5),
s=(2 5)(3 4),
```

and let `chi:D10->C2` kill the rotations and send every reflection to the
nontrivial element.  The graph

```text
L={(h,chi(h)):h in D10}<G
```

has order ten.  On the twelve cosets `G/L`, both order-six subgroups above act
freely, so each restriction is `2 Reg`.

This explains the failure mode structurally: the three queried words only test
whether two local order-six subgroup pictures can be glued, and `A5 x C2`
contains a non-A8 gluing which passes them exactly.
