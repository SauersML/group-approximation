---
rg: 2
id: atlas-packet-energy-controls-s3-covariance
kind: claim
title: Packet commutator energy quantitatively controls the two raw S3 covariance defects
distinct_from:
  atlas-packet-forces-two-s3-covariance-energy: that is the opposite lower bound forced by collision 19243; this claim is a purely representation-theoretic upper bound from packet commutators.
---

Let `lambda_k=Reg(A8) tensor I_k`, let `S` be the ten packet letters, and let
`h_a,h_b` be the fixed generators of the raw S3 slice.  For every unitary `U`
put

```text
E_packet(U) = sum_(s in S) ||U lambda_k(s)-lambda_k(s) U||_2^2,
a(U) = ||U lambda_k(h_a) U^*-lambda_k(h_a)||_2,
b(U) = ||U lambda_k(h_b) U^*-lambda_k(h_b)||_2.
```

Then, uniformly in the external multiplicity,

```text
a(U)^2+b(U)^2 <= (28363/1260) E_packet(U).             (PACKET->S3)
```

Consequently packet commutator energy tending to zero forces the exact two S3
covariance coordinates used by the shortest nonhyperlinear atlas route to tend
to zero.  Numerically, it is already enough for

```text
E_packet(U) < 1260/(128*28363)
```

to beat the asymptotic `1/128` collision-19243 floor.
