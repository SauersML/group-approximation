---
rg: 2
id: compressed-k2m-deficit-is-one-aggregate-sign-row-proof
kind: route
title: Aggregate the synchronized source cuts and apply the hard-sign estimate
target: compressed-k2m-deficit-is-one-aggregate-sign-row
requires:
  - compressed-k2m-locks-gauge-but-needs-matrix-separator
  - hard-sign-transport-captures-exit-mass
---

Use the synchronized factorization of
`compressed-k2m-locks-gauge-but-needs-matrix-separator` and put

```text
S_j=B_jG_jB_j^*,       S=sum_j S_j.
```

The `S_j` are orthogonal, so `S` is a projection and
`tau(S)=sum_j tau(G_j)`.  Since `S_jS=S_j`, orthogonality also gives

```text
||(I-C)A_1S||_2^2
 =sum_j ||(I-C)A_1S_j||_2^2
 =sum_j ||(I-C)A_1B_jG_j||_2^2,                        (KAP1)
```

which is `(KAS2)`.

Apply the elementary hard-sign transport inequality to the source projection
`S`, source involution `R_S=I-2S`, target involution `R_C=I-2C`, and unitary
`A_1`.  Because `R_SS=-S`, it gives

```text
tau(S)-tau(CA_1SA_1^*)
 <= ||(I-C)A_1S||_2^2
 <= (1/4)||R_CA_1-A_1R_S||_2^2.                        (KAP2)
```

Also `tau(CA_1SA_1^*)<=tau(C)`, hence

```text
tau(S)-tau(C)
 <= ||(I-C)A_1S||_2^2.
```

Substituting `tau(S)=sum_j tau(G_j)` and multiplying the intertwining defect
on the right by the unitary `R_SA_1^*` gives exactly `(KAS3)`:

```text
sum_j tau(G_j)-tau(C)
 <= ell_sync
 <= (1/4)||R_C A_1R_SA_1^*-I||_2^2.
```

Thus the entire synchronized source-capacity surplus is paid by one aggregate
binary covariance row.