---
rg: 2
id: atlas-a4-two-component-commutant-gluing
kind: claim
title: The S3 and S3xC3 packet commutants glue uniformly to the full A8 commutant
---

Let `H_6,H_18 < A8` be the two packet-component subgroups from
`atlas-a4-packet-biclique-decomposition`, and let

```text
lambda_k = Reg(A8) tensor I_k.
```

There is a constant `C_comp<infinity`, depending only on the two fixed
subgroups and not on `k`, such that every matrix `X` satisfies

```text
dist_2(X,lambda_k(A8)')^2
 <= C_comp * (
      dist_2(X,lambda_k(H_6)')^2
    + dist_2(X,lambda_k(H_18)')^2 ).                  (A4-COMP-GLUE)
```

Thus an external multiplicity cannot hide a relative chart frame which is
simultaneously close to the two component commutants.  Since

```text
H_6 ~= S3,
H_18 ~= S3 x C3,
```

the packet synchronization problem may be attacked on these two small finite
representation categories and glued only at the end.
