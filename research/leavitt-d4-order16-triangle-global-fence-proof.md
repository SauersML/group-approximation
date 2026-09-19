---
rg: 2
id: leavitt-d4-order16-triangle-global-fence-proof
kind: route
title: Capture the gauge or separate long and short carrier factors
target: leavitt-d4-order16-triangle-global-fence
requires:
  - leavitt-d4-metacyclic-retraction-leak
---

Let `M=<w,z>` with

```text
w^16=1,  z w z^-1=w^-3,  z^4=w^12,
```

and let `x=w^2z`.  Every solution in the projection family has one free
gauge `k` and

```text
b=k,  a=kx,  d=kxw,  c=kxwz.                         (1)
```

The four elements `1,x,xw,xwz` are distinct in the faithful affine action
on `Z/16`; in particular the three nonidentity ratios in (1) never vanish.

Write

```text
H=b_0c_1d_2a_3,       Ki=H^-1 Bi,       J=H^-1.
```

Each residual has factor triple `(H,Ki,J)`.  Enumerating the six
cyclic/inverse placements of the canonical triangle factors is purely
combinatorial.  Unless every face uses orientation 0 or its whole inverse 3,
one carrier is required to identify some `Ki^(+-1)` with `H` or `J`.

Suppose first that `k` is not in `M`.  Then all four units in (1) are
nonidentity.  Both `H` and `J` have four free-product blocks, whereas every
`Ki` has seven: the only middle products are `x`, `xw`, or `xwz`, all
nonidentity.  Thus the required long-short carrier identification is
impossible.  For the remaining eight orientation triples in `{0,3}^3`,
direct free-product reduction gives respectively

```text
19, 19, 13, 19, 13, 13, 13, 19
```

blocks in lexicographic orientation order.  No displayed block can vanish:
it is either a nonidentity word of `M`, a unit `k m` or `m k^-1` (whose
vanishing would put `k` in `M`), or a conjugate by `k` of a nonidentity word
of `M`.  Hence none is a one-copy boundary.

If `k` lies in `M`, the affine action shows `|M|=64` and gives every element
faithfully as a twenty-leaf permutation unit.  The exact auditor
`research/artifacts/verify-degree4-metacyclic-retraction-leak.py` exhausts
all 64 gauges and all `6^3` orientations; none gives a one-copy nonidentity
boundary.  These two cases exhaust arbitrary ambient coefficient groups.

