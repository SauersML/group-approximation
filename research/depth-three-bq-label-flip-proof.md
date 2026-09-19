---
rg: 2
id: depth-three-bq-label-flip-proof
kind: route
title: Expand D:33 and conjugate every arm and child by the depth-three swap
target: depth-three-bq-arm-expansion-is-equivariant-under-label-flip
requires: []
---

All prefixes in `(DTE1)` are pairwise incomparable where required.  The
Bleak--Quick definitions give the identities in `(DTE2)` directly:

* D:33 defines `r`, `s_i`, `s_j`, `t_j`, and the adjacent-child swap `f`;
* D:other33 with ordered blocks `01,00`, child bits `0,1`, and
  `rho_(01,00)=a` gives `t_i=tau_(000,011)^a`.

The general depth-three conjugacy relation for swaps sends both endpoints by
the conjugating swap.  Since `r=(000,001)` is disjoint from
`f=(010,011)`, it is fixed.  The same rule gives

```text
(010,000)^f=(011,000),       (010,001)^f=(011,001),
```

which proves `(DTE4)` and transports `(DTE3)` as a whole.  The split
relations in `(DTE5)` are the defining identity

```text
tau_(alpha,beta)
 =tau_(alpha0,beta0) tau_(alpha1,beta1).
```

The action of `f` on every descendant changes the initial prefix `010` to
`011` while fixing `000` and `001`, so both child factors move.  No child is
common.

For `(DTE6)`, the listed source and target sets are maximal prefix codes.
The prefix replacement `g` carries the ordered three-cycle of source
cylinders `(01,10,11)` to `(010,000,001)` and carries its fixed complement
onto the fixed complement.  Therefore `b^g=c_i`.  Postcomposing the target
chart with `f` replaces `010` by `011` and fixes `000,001`, proving
`b^(gf)=c_j`.

Every calculation is an exact equality in `V`; the five-dimensional
standard representation from
`bare-r5-a6-collision-label-swap-countermodel` then witnesses positive
operator mismatch while all these canonical arm identities remain exact.

