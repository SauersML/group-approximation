---
rg: 2
id: sl3-self-commutator-s3-leak-proof
kind: route
title: Realize the self-commutator packet in the regular representation of S3
target: sl3-self-commutator-overlap-packet-has-s3-leak
requires: []
---

In `S_3`, let

```text
w=(123),       z=(12),       x=z.
```

Conjugation by `z` inverts `w`.  With the convention
`[a,b]=aba^(-1)b^(-1)`,

```text
[w,z]=w z w^(-1) z=w^2=w^(-1).
```

Therefore

```text
x[w,z]x^(-1)=z w^(-1) z=w.
```

Also `z^4=x^2=1`, so both overlap-power commutators in `(S3L1)` vanish.
Apply the left regular representation of `S_3`.  All identities remain
exact and, since `w` is nonidentity, its normalized regular trace is zero.
This proves `(S3L2)`.

