---
rg: 2
id: atlas-a4-gl5-packet-collision-screen-proof
kind: route
title: Exhaust the 496 GL5/GL4 cosets with exact conjugacy-class masks
target: atlas-a4-gl5-packet-collision-screen
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_a4_gl5_packet_screen.py
---

The replay script performs a finite exhaustive calculation over `F2`.

The standard embedded chart `H=GL4(F2)` has index

```text
|GL5(F2):H| = 496.
```

A right coset is represented canonically by a line `l` and a complementary
hyperplane `ker(phi)` with `phi(l)=1`; there are exactly `31*16=496` such
pairs.  Thus every `h in GL5(F2)` is represented exactly once as

```text
h = h_0 k,   k in H,
```

for one of the 496 stored representatives `h_0`.

The thirty packet occurrences reduce to sixteen distinct ordered pair
constraints.  The moving factor-two alphabet has four involutions and six
order-three elements.  Exact conjugation inside `H` shows that the former all
belong to one conjugacy class of size `105`, and the latter to one class of
size `1120`.  For each coset representative, the script computes exactly which
members of those classes satisfy `(xy)^3=1` against the fixed factor-one
letter, then intersects the resulting Boolean masks over all sixteen pair
constraints for all `20,160` possible internal alignments `k`.

This exhausts all

```text
496 * 20160 = 9,999,360 = |GL5(F2)|
```

relative positions without random sampling.  Exactly 202 masks survive.  The
script then directly evaluates collision 19243 on each survivor and computes
`H intersect hHh^-1` by exact matrix enumeration.  The asserted histograms are
hard-coded as replay invariants; any changed count raises an exception.

No floating-point arithmetic, numerical tolerance, optimizer or unproved group
classification enters the certificate.
