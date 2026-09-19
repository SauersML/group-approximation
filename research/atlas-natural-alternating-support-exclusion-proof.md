---
rg: 2
id: atlas-natural-alternating-support-exclusion-proof
kind: route
title: Classify the A4 orbit packet and use generation by the six order-three letters
target: atlas-natural-a8-supports-collapse-before-collision
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-a4-19243-classical-collapse
artifacts:
  - experiments/atlas_a4_natural_support_certificate.py
---

The exact packet audit now records three additional facts.  There are six
distinct order-three packet labels; their closure in `GL_4(2)` has order
20160; and their ambient centralizers all have order 18.  Every packet
involution has ambient centralizer 192.  Under `GL_4(2) ~= A8`, the two
order-three cycle types `3` and `3^2` have centralizer orders 180 and 18,
while the two involution cycle types `2^2` and `2^4` have centralizer orders
96 and 192.  Thus the packet types are exactly `3^2` and `2^4`, and the six
order-three letters generate `A8`.  Automorphisms of `A8` are induced by
`S8`, so arbitrary chart markings preserve these cycle types.

Fix one packet edge.  Its generators retain exact orders two and three, and
the pair-cube relation makes their image a quotient of the `(2,3,3)` triangle
group `A4`.  No proper quotient of `A4` retains both orders, so the generated
group is `A4`.

Classify its transitive permutation orbits.  Apart from fixed points, the
possible orbit degrees are `3,4,6,12`, corresponding to stabilizers
`V4,C3,C2,1`.  On these orbits, the numbers of 3-cycles of `a` and
transpositions of `b` are respectively

```text
degree             3      4      6      12
a: number 3-cycles 1      1      2       4
b: transpositions  0      2      2       6.          (NAO4)
```

Let the multiplicities of these orbit types be `x,y,z,w`.  The global cycle
types `a=3^2` and `b=2^4` give

```text
x+y+2z+4w=2,
2y+2z+6w=4.                                         (NAO5)
```

The unique nonnegative solution is

```text
x=z=w=0,       y=2.                                 (NAO6)
```

Thus `<a,b>` has two natural four-point orbits.  Their union is the full
eight-point support of `b`, and `a` moves three points in each orbit, proving
`supp(a) subset supp(b)`.

Now place the first chart on `X` and the second on `Y`.  Each of the six
order-three packet labels in the first chart occurs on an edge with a
second-chart involution.  The support containment puts all six supports in
`Y`; their generation of `Alt(X)` forces `X subset Y`, hence `X=Y`.
The relative marking is now an automorphism alignment of one `A8`.  The
established classical-collapse theorem says no such alignment satisfies the
packet and `q_19243`.  This proves the claim.
