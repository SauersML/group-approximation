---
rg: 2
id: strict-idempotent-equivalence-proof
kind: route
title: Pad a strict corner equivalence by the complementary idempotent
target: strict-idempotent-equivalence-breaks-direct-finiteness
requires: []
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

## Direct proof

Given `xy=p` and `yx=q<p`, both `x` and `y` lie in `pTp`.  Hence

```text
X=x+(1-p),        Y=y+(1-p)
```

have vanishing cross terms and satisfy

```text
XY=p+(1-p)=1,
YX=q+(1-p) != 1.
```

For the inner-compression specialization, if `q=wpw^(-1)`, direct
multiplication gives

```text
(pw^(-1)q)(qwp)=p,        (qwp)(pw^(-1)q)=q,
```

so the general criterion applies.
