---
rg: 2
id: atlas-a4-packet-commutant-synchronization-proof
kind: route
title: Diameter-nine packet generation plus A8 averaging gives the commutant gap
target: atlas-a4-packet-commutant-synchronization
requires:
  - atlas-a4-packet-letters-generate-both-a8-charts
artifacts:
  - experiments/atlas_a4_packet_generation.py
---

Fix one chart and write `lambda=lambda_k`.  By the exact packet-generation
audit, the ten-letter packet set `S` generates `A8` and every `g in A8` is a
directed word

```text
g=s_1 ... s_l,   s_i in S,   l<=9.                    (1)
```

For `||X||_op<=1`, commutator telescoping along `(1)` gives

```text
||[X,lambda(g)]||_2
 <= sum_(i=1)^l ||[X,lambda(s_i)]||_2
 <= 9 (sum_(s in S)||[X,lambda(s)]||_2^2)^(1/2).       (2)
```

The last inequality is deliberately coarse but explicit: each summand is at
most the displayed Euclidean norm and there are at most nine summands.

Now average over the regular chart action:

```text
E(X)=(1/|A8|) sum_(g in A8) lambda(g) X lambda(g)^*.
```

This is the Hilbert--Schmidt orthogonal conditional expectation onto
`lambda(A8)'`.  Therefore

```text
dist_2(X,lambda(A8)')
 <= ||X-E(X)||_2
 <= (1/|A8|) sum_g ||X-lambda(g)Xlambda(g)^*||_2
 <= 9 (sum_(s in S)||[X,lambda(s)]||_2^2)^(1/2)
```

by `(2)`.  The exact audit also shows that the two chart factors use the same
ten-letter packet alphabet, so the same constant `9` applies on both sides and
is independent of the external regular multiplicity.