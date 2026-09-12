---
rg: 2
id: common-pivot-r2-output-uniqueness-proof
kind: route
title: Classify transpositions by their action on the two-point input support
target: common-pivot-r2-output-transposition-is-unique
requires: []
---

For a permutation `u`, conjugation sends a transposition supported on a
two-point set `A` to the transposition supported on `u(A)`.  Thus
`t(i p)t=(p q)` implies

```text
{t(i),t(p)}={p,q}.
```

If the transposition `t` moves `p`, it swaps `p` either with `q`, giving
image support `{i,q}`, or with `i`, leaving `{i,p}` unchanged; swapping `p`
with any other letter also leaves `i` in the image support.  All cases
contradict `{t(i),t(p)}={p,q}`.  Therefore `t` fixes `p`, so it must swap `i`
and `q`.  This proves `t=(i q)`.

The depth-three identification and label flip are the exact equalities in
`depth-three-bq-arm-expansion-is-equivariant-under-label-flip`; applying the
classification to them gives the stated private-endpoint obstruction.

