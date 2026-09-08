---
rg: 2
id: jacobson-natural-head-permutation-gap-is-sqrt-three
kind: claim
title: Natural seven-point head permutation packets have sharp two-braid gap sqrt three
distinct_from:
  jacobson-two-braid-mixed-packet-gap: that asks for positivity over all finite-dimensional unitary packets; this proves a sharp bound only when the head is the natural seven-point permutation action and the completion preserves the product basis, and supplies an upper bound for the unrestricted infimum.
  jacobson-mixed-packet-attains-rank-eight-below-two: that gives a twelve-dimensional cyclotomic unitary example with marked rank eight and both defects below two; this gives an explicit 56-point permutation example with marked rank sixteen, exact tail braid, and first defect exactly sqrt three, together with a sharp lower bound for its entire permutation class.
  del2-three-dimensional-head-braid-gap: that bounds all unitary overlap involutions for the two three-dimensional head types; this concerns the natural seven-point permutation head and assumes the overlap involution is itself a permutation in the specified basis.
  jacobson-two-braid-infimum-is-zero: that constructs marked MF asymptotic models with unrestricted unitary packets and proves the universal infimum is zero; this proves a sharp positive lower bound only for a specified permutation basis class, which those asymptotic models must escape.
artifacts:
  - research/artifacts/jacobson-natural-head-permutation-gap-2026-09-08.md
  - research/artifacts/jacobson-56-point-two-braid-2026-09-08.json
  - experiments/jacobson_56_point_two_braid_search.py
---

Let `G=GL_3(F_2)` and let `T` be any nonempty finite `G`-set. On the
product packet `(F_2^3\{0}) x T`, let `H` be a permutation involution
commuting with `K=GL(<e_1,e_3>)_Q`. For

```text
B=(w_23,w_23),                D=(1,w_13),
```

the first braid always has operator-norm defect

```text
||(HB)^3-I|| >= sqrt(3).
```

An explicit choice with `|T|=8` attains equality, satisfies
`(HD)^3=I`, and retains the mark `(I+E_13,1)` with negative rank
sixteen. Hence the infimum of the maximum of the two defects in this
specified permutation class is exactly `sqrt(3)`. The same value holds
if the tail braid is required to be exact.

In the unrestricted notation of
`jacobson-two-braid-gap-characterizes-mark-collapse` and
`jacobson-tail-braid-exactification-and-standard-carrier`,

```text
gamma <= gamma_tail <= sqrt(3).
```

The lower bound does not apply to arbitrary unitary involutions, even
on the displayed packet. The independent
`jacobson-two-braid-infimum-is-zero` proves that the unrestricted
numbers are both zero; its asymptotic models must escape this specified
permutation class.
