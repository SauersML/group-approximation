---
rg: 2
id: relative-leavitt-active-subspace-expansion-proof
kind: route
title: Apply the two left inverses to the binary branch sum
target: relative-leavitt-active-subspaces-expand-by-two
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
---

Suppose `s_0v_0+s_1v_1=0` with `v_0,v_1 in V subset AR`.  Multiplication on
the left by `t_j` gives

```text
0=t_j(s_0v_0+s_1v_1)
  =(t_js_0)v_0+(t_js_1)v_1
  =A v_j=v_j.
```

Thus both `v_0` and `v_1` vanish, proving `(LAS1)`.  Its image is exactly
`s_0V+s_1V`, so rank--nullity gives `(LAS2)`.  If `W` contains that image,
then `(LAS3)` follows immediately.
