---
rg: 2
id: conjugacy-addressed-opnorm-challenges-are-lossless-proof
kind: route
title: Evaluate the free conjugate and use unitary invariance of operator norm
target: conjugacy-addressed-opnorm-challenges-are-lossless
requires: []
---

For a free word `a`, `a(U)` is unitary. Therefore

```text
(a^-1 r a)(U)-I
 = a(U)^-1 (r(U)-I) a(U).
```

Unitary invariance of operator norm gives `(COC1)`. Applying `(COC1)` to each
identity `(COC2)` and taking the supremum proves `(COC3)`.
