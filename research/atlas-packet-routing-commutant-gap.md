---
rg: 2
id: atlas-packet-routing-commutant-gap
kind: claim
title: Low-congestion packet routing sharpens the regular A8 commutant test
artifacts:
  - experiments/atlas_packet_commutant_routing.py
distinct_from:
  atlas-a4-packet-commutant-synchronization: that uses only the worst-case packet word diameter nine; this claim exploits the exact congestion of a simultaneous routing of all A8 elements through the same packet alphabet.
---

Fix either regular chart

```text
lambda_k = Reg(A8) tensor I_k
```

and let `S` be the common ten-letter A4 packet alphabet.  For every matrix `X`
(on every multiplicity `k`, with no operator-norm hypothesis),

```text
dist_2(X, lambda_k(A8)')^2
 <= (28363/10080)
    * sum_(s in S) ||X lambda_k(s)-lambda_k(s) X||_2^2.   (PACKET-ROUTE)
```

Equivalently the coefficient in front of the root-sum-square packet
commutator energy is

```text
sqrt(28363/10080) < 1.678,
```

instead of the diameter-only coefficient `9`.

The constant is certified by an exact shortest-word routing of all `20160`
group elements.  If `n_s(g)` is the number of occurrences of packet letter
`s` on the frozen shortest path to `g`, the largest weighted congestion is

```text
max_s sum_(g in A8) |w_g| n_s(g) = 113452.
```

Since `2|A8|=40320`, the coefficient squared is exactly
`113452/40320 = 28363/10080`.
