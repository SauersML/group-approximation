---
rg: 2
id: atlas-natural-a8-supports-collapse-before-collision
kind: claim
title: The Atlas packet and collision exclude every pair of natural support A8 subgroups in every alternating group
artifacts:
  - experiments/atlas_a4_natural_support_certificate.py
distinct_from:
  atlas-seven-word-a9-a10-exclusion: that exhausts all marked chart positions in the two smallest natural alternating overgroups; this proves a support-theoretic exclusion simultaneously in every A_n for the full A4 packet.
  atlas-a4-19243-classical-collapse: that treats two markings of one A8 subgroup; this proves that the packet first forces any two natural support subgroups to coincide, then invokes that collapse.
  atlas-q14-simple-overgroup-index-is-at-least-32: that permits three abstract intersection types at the first surviving index; this rules out all of them in the natural alternating-support family.
---

Let `X,Y` be eight-element subsets of `{1,...,n}` and let

```text
A=Alt(X),   B=Alt(Y) < A_n,                           (NAO1)
```

with arbitrary marked identifications of the two abstract atlas charts with
`A` and `B`.  If all twelve distinct cross-`A4` packet edges hold, then

```text
X=Y,       A=B.                                      (NAO2)
```

Consequently no such pair satisfies the packet together with collision
`q_19243`; a fortiori none satisfies packet plus `q_19243` plus q14 or
generates a larger alternating simple group.

The mechanism is exact and label-independent.

1. Every packet involution is in the `2^4` class of natural `A8`, and every
   packet order-three letter is in the `3^2` class.
2. If permutations `b` of type `2^4` and `a` of type `3^2` satisfy one packet
   edge, then `<b,a> ~= A4` and its permutation action is exactly two natural
   four-point `A4` orbits plus fixed points.  Hence

   ```text
   supp(a) subset supp(b).                            (NAO3)
   ```
3. The six distinct order-three packet letters alone generate the whole
   chart `A8`.

Applying `(NAO3)` to every order-three letter in `A` and its adjacent
involution in `B` puts the support of every one of those six letters inside
`Y`.  Since they generate `A=Alt(X)`, their combined support is `X`, so
`X subset Y`.  Both sets have size eight, proving `(NAO2)`.

At the first abstract index-32 residue this gives a particularly clean
exclusion.  Natural support intersections are `Alt(X intersect Y)`.  The
abstract types `2^3:GL_3(2)` and `S6` cannot occur in this family, while the
`A7` case would have `|X intersect Y|=7`; the packet already forces overlap
eight.  Thus no natural alternating realization reaches either index-32
profile.

For standard binary-linear overgroups, the corresponding first two rank
enlargements are already separately excluded: the full packet plus collision
has no standard `GL5(2)` completion, and even the rank-three core, collision,
and one forward central-`C3` packet edge have no standard `GL6(2)` completion.
The present theorem does not classify nonstandard `A8` embeddings in higher
classical groups.
