---
rg: 2
id: raw-swap-forces-s3-reynolds-deficit-one-over-320-proof
kind: route
title: Combine the raw two-direction energy floor with the Reynolds-distance bound
target: raw-swap-forces-s3-reynolds-deficit-one-over-320
requires:
  - raw-swap-forces-two-s3-covariance-energy
  - two-generator-covariance-controls-reynolds-deficit
---

Let `a_n,b_n` be the two named covariance defects.  The raw-word telescope
gives

```text
a_n^2+b_n^2 >= 1/40-o(1).
```

Apply `two-generator-covariance-controls-reynolds-deficit` to the subgroup
`K=<h_a,h_b>`:

```text
a_n^2+b_n^2
 <= 8(1-||E_K(U_n)||_2^2).
```

Dividing by eight yields

```text
1-||E_K(U_n)||_2^2 >= 1/320-o(1),
```

which is `(SR320)`.
