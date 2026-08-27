---
rg: 2
id: leavitt-target-return-channel-count-firewall-proof
kind: route
title: Compare the trace capacity of each target-return channel with the source Reynolds rank
target: leavitt-target-return-channel-count-firewall
requires: []
---

For every supported contraction `X=R_tXR_s`, the positive operator
`XX^*` is bounded by `R_t`.  Cyclicity of the finite normalized adjoint
trace therefore gives

```text
tr_ad(X^*X)=tr_ad(XX^*)<=tr_ad(R_t)=p^(-4).
```

Summing this inequality with nonnegative weights proves `(TCF4)`, and
comparison with `tr_ad(R_s)=p^(-2)` proves the channel lower bound.  The
orthogonal decomposition and partial isometries in `(TCF9)` attain equality
with exactly `p^2` channels, proving sharpness.
