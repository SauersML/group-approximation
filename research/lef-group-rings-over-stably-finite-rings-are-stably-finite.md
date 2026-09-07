---
rg: 2
id: lef-group-rings-over-stably-finite-rings-are-stably-finite
kind: claim
title: LEF group rings preserve stable finiteness of arbitrary coefficient rings
distinct_from:
  rf-lamps-preserve-stable-finiteness-for-arbitrary-actions: that uses separating global finite lamp quotients; this transfers a hypothetical finite inverse witness through a partial multiplication table and only assumes LEF lamps.
---

Let R be a stably finite unital ring, possibly noncommutative, and A a
LEF group. Then the ordinary group ring R[A] is stably finite. Group
labels commute with R in this statement; it is not a skew group ring.

Here LEF means that every finite subset E of A has an injective map
into a finite group preserving each product a b=c with a,b,c in E.
No globally defined finite quotient of A is required. A finite inverse
witness involves only a finite multiplication table, which transfers
exactly to a finite group algebra over R.

Consequently, for any field k, any group G, any G-set X, and any LEF A,

    k[A wr_X G] is stably finite iff k[G] is stably finite.

The wreath product is restricted and its action only permutes lamp
coordinates. The diagonal tensor induction needs stable finiteness of
k[A^j x H] for every finite j and H<=G. Finite products of LEF groups
are LEF, so the coefficient-ring theorem supplies precisely these base
cases with R=k[H].

Thus independent finite-pattern computational libraries cannot create
stable nonfiniteness over a stably finite base by this construction,
even when their finite models do not come from compatible global
quotients. This statement supplies no extension to arbitrary internal
automorphism twists on LEF lamps, nonsplit group extensions, or
unrestricted wreath products. Neither headline conjecture is resolved.
