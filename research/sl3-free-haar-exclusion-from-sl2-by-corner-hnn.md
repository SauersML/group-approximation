---
rg: 2
id: sl3-free-haar-exclusion-from-sl2-by-corner-hnn
kind: route
title: The SL3 free-Haar exclusion follows from the SL2 one because the SL2 HNN group sits inside the SL3 HNN group
target: sl3-hnn-admits-no-amalgamated-free-haar-unitary
requires:
  - sl2-hnn-admits-no-amalgamated-free-haar-unitary
  - hnn-hyperlinearity-is-amalgamated-free-haar-unitary
  - dyadic-hnn-family-is-monotone-in-rank-and-primes
---

By `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`,
`sl2-hnn-admits-no-amalgamated-free-haar-unitary` says exactly that

```text
G_2 = < SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1 >
```

is not hyperlinear. By `dyadic-hnn-family-is-monotone-in-rank-and-primes` (MON3) with
`(n,S) = (2,{2}) <= (3,{2})`, `G_2` embeds in

```text
G_3 = < SL_3(Z[1/2]), t | [t, SL_3(Z)] = 1 >.
```

A group containing a nonhyperlinear subgroup is nonhyperlinear, so `G_3` is not
hyperlinear. Again by `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`, no
regular-trace matrix model of `SL_3(Z[1/2])` carries an amalgamated-free Haar unitary in
the `SL_3(Z)`-centralizer. That is the target.

The route is conditional on the OPEN SL_2 claim and fires only if that claim is
established. The converse direction is not available: a proof at SL_3 does not give SL_2.
