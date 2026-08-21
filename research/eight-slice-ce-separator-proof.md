---
rg: 2
id: eight-slice-ce-separator-proof
kind: route
title: Compare the universal overlap floor with the proposed matrix upper bound
target: eight-slice-overlap-requires-a-connes-embedding-separator
requires: []
---

Let

```text
F=tau(S)-tau(SW^*CWS).
```

The eight-slice packet calculation holds in every tracial representation
and gives

```text
F>=tau(S)-tau(C)=tau(P_f)/16.
```

Assume the desired finite-dimensional estimate

```text
F<=K E_rel+o(1).
```

Passing any sequence of matrix approximate representations to a tracial
ultraproduct sets `E_rel=0`, hence `F=0`.  The universal lower bound then
kills the image of `P_f`.  If the shared non-CE BCS gap forces positive total
forbidden mass whenever the native mark survives, no matrix-ultraproduct
representation can preserve that mark.

In the canonical regular representation `tau(P_f)>0`, so the same lower
bound makes `F>0`; consequently the matrix estimate fails there.  It is
therefore exactly a trace-polynomial separating matrix ultraproducts from
the marked regular model.  A universal tracial positivity certificate would
also hold in the regular model and contradict this calculation.  This
establishes the claimed logical status without asserting the still-open
matrix inequality.
