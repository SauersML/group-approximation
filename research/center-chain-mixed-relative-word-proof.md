---
rg: 2
id: center-chain-mixed-relative-word-proof
kind: route
title: Check every mixed Hecke root rectangle against the marked indices
target: center-chain-mixed-relative-word-fixes-mark
requires:
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
---

The center-chain definitions are

```text
A_1=x_47(a_1),       A_2=x_58(a_2),
B_2=x_84(b_2),       B_3=x_95(b_3).
```

All four root rectangles lie entirely in `K`.  Against `z=x_13(q)`, neither
of the composable Steinberg patterns `j=k` nor `i=l` can occur: no factor
has index `1` or `3`.  Hence every factor commutes with `z`.  Products and
inverses of centralizing elements still centralize, proving `(CMF2)` for
`u_1,u_2,U`.

The extra full-word factor in the tail removal is
`g_1=x_87(s_(00)t_0)`, whose indices are also in `K`; thus it and the
displayed product `g_1B_3A_2` centralize `z` as well.  Compression by `Q`
does not change the preceding group-word identity.  Since a nonzero root in
a rectangle disjoint from `{1,3}` has a distinct elementary-matrix image
from `z`, `(CMF2)` cannot satisfy the disjoint-root hypothesis.
