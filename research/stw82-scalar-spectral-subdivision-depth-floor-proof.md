---
rg: 2
id: stw82-scalar-spectral-subdivision-depth-floor-proof
kind: route
title: Count one active scalar band from every original colour at each spectral point
target: stw82-scalar-band-depth-floor
requires: []
---

Fix `t in X`.  For every original colour `v`, (D1) supplies at least one
index `j(v)` with

```text
g_(v,j(v))(t)>0.
```

Thus `t` belongs to the cozero set of `g_(v,j(v))`, and hence to
`J_(v,j(v))`.  The pairs `(v,j(v))` are distinct as `v` varies, so at least
`N` bands contain `t`.  This proves the pointwise version of (D2), hence
(D2) itself.

For exact scalar partitions of unity take `eta=1`.  If the sum for each
original colour is within norm less than one of the constant function one,
then (D1) holds with a positive `eta`, so the same lower bound is stable
under such approximate reconstruction.  Substituting
`N=(p+1)+(q+1)` gives the extension-colour statement.
