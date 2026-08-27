---
rg: 2
id: tracial-projective-hilbert-hotel-cancellation-proof
kind: route
title: Apply faithful finite trace dimension to a projective self-copy
target: tracial-projective-hilbert-hotel-cancellation
requires: []
---

Write `P=p M^k` for a projection `p in M_k(M)`.  Its finite dimension is

```text
dim_tau(P)=(tau tensor Tr_k)(p).
```

Murray--von Neumann equivalent projections have equal dimension, direct sum
adds dimensions, and faithfulness of the ultraproduct trace gives
`dim_tau(P)=0` only for `P=0`.  An isomorphism with `m` copies therefore
implies

```text
dim_tau(P)=m dim_tau(P),
```

so `dim_tau(P)=0` and `P=0`.

For a binary Leavitt family, its two synthesis maps and two analysis maps
give mutually inverse module maps between `P` and `P directSum P`, exactly as
in the norm-corona projective cancellation theorem.  Hence a unital action
forces `P=0`.
