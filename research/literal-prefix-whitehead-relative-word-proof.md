---
rg: 2
id: literal-prefix-whitehead-relative-word-proof
kind: route
title: Use the disjoint root rectangles and the adjacent-transposition braid
target: literal-prefix-whitehead-relative-word-fixes-mark
requires:
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
  - adjacent-prefix-whitehead-braid-conjugates-reservoir-gauges
---

Every elementary factor of `W_m` has both root indices in
`{k_1,k_2,k_3}`, whereas `z=x_13(q)` has indices `{1,3}`.  These rectangles
have neither composable index pattern.  The ordinary Steinberg commutator
relation therefore gives

```text
[W_1,z]=[W_2,z]=1.                                      (1)
```

The centralizer of `z` is a subgroup, so `(1)` proves `(LPF2)` for every
`g_1,g_2 in Omega`.  A nonzero root in a position disjoint from `{1,3}` is
not `z`: their images in the elementary matrix quotient have their unique
nonzero off-diagonal entries in distinct positions.  Hence `(LPF2)` and
`(LPF3)` are incompatible.

For the adjacent pair, the established partial-swap calculation gives

```text
W_1^2=W_2^2=1,
W_1W_2W_1=W_2W_1W_2.
```

Consequently `u=W_1W_2` and

```text
u^3=W_1W_2W_1W_2W_1W_2
   =W_2W_1W_2W_2W_1W_2=1,
```

while `(1)` still gives `uzu^(-1)=z`.  Finally, a product of elements in
the centralizer of `z` remains there, proving the assertion about fixed
packet relabelings.  A dressing outside this centralizer is not a
consequence of the displayed prefix packet and must be authenticated by an
additional occurrence row; no such row is used here.
