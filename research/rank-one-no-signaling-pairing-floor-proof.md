---
rg: 2
id: rank-one-no-signaling-pairing-floor-proof
kind: route
title: Apply the two Bernoulli Fréchet bounds at the shared endpoints
target: rank-one-no-signaling-pairing-floor
requires: []
---

The diagonal successes are contained in their named endpoint events, so

```text
mu_00(1,1) <= a,       mu_11(1,1) <= b.
```

Consequently

```text
p_00 >= 1-a,           p_11 >= 1-b.                  (1)
```

For the middle law, the Fréchet lower bound for two Bernoulli events gives

```text
p_01 = mu_01(1,1) >= max(0,a+b-1).                   (2)
```

Summing `(1)` and `(2)` yields

```text
p_00+p_01+p_11
 >= 2-a-b+max(0,a+b-1) >= 1,
```

proving `(RNS2)`.  For uniform source labels, restrict the error average to
the source pair `(1,1)` and discard every other nonnegative contribution.
This gives the first inequality in `(RNS3)`; one of three nonnegative terms is
then at least one third of their sum.
