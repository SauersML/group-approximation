---
rg: 2
id: atlas-packet-routing-commutant-gap-proof
kind: route
title: Average displacement over A8 and charge each shortest path by packet-letter congestion
target: atlas-packet-routing-commutant-gap
requires:
  - atlas-a4-packet-letters-generate-both-a8-charts
artifacts:
  - experiments/atlas_packet_commutant_routing.py
---

Write `G=A8`, `N=|G|=20160`, and suppress the amplification index.  Let

```text
E(X) = (1/N) sum_(g in G) lambda(g) X lambda(g)^*
```

be finite-group averaging.  It is the Hilbert--Schmidt orthogonal projection
onto `lambda(G)'`.  Therefore

```text
(1/N) sum_g ||X-lambda(g)Xlambda(g)^*||_2^2
 = 2 ||X-E(X)||_2^2.                                   (1)
```

For every `g`, freeze the shortest packet word

```text
w_g=s_1 ... s_l
```

constructed by `experiments/atlas_packet_commutant_routing.py`.  Telescoping
conjugation along the word and using unitary invariance of normalized HS norm
gives

```text
||X-lambda(g)Xlambda(g)^*||_2
 <= sum_(j=1)^l ||X-lambda(s_j)Xlambda(s_j)^*||_2.
```

Cauchy--Schwarz then yields

```text
||X-Ad(g)X||_2^2
 <= l sum_(j=1)^l ||X-Ad(s_j)X||_2^2.                  (2)
```

For a packet letter `s`, let `n_s(g)` be its number of occurrences in `w_g`.
Insert `(2)` into `(1)` and collect equal packet letters:

```text
2 ||X-E(X)||_2^2
 <= sum_(s in S)
      [(1/N) sum_g |w_g| n_s(g)] ||X-Ad(s)X||_2^2.    (3)
```

The exact integer audit reaches all `20160` elements and certifies

```text
max_s sum_g |w_g| n_s(g) = 113452.
```

Hence `(3)` gives

```text
||X-E(X)||_2^2
 <= 113452/(2*20160) * sum_(s in S) ||X-Ad(s)X||_2^2
 = 28363/10080 * sum_(s in S) ||X-Ad(s)X||_2^2.
```

Finally `||X-Ad(s)X||_2=||Xlambda(s)-lambda(s)X||_2`.  Tensor amplification
only repeats the same left-regular action and preserves every normalized-HS
identity above, so the constant is independent of `k`.
