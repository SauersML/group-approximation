---
rg: 2
id: leavitt-degree4-five-corner-full-packet-is-absent
kind: claim
title: Neither minimal degree-four five-corner topology accepts the full Leavitt packet
artifacts:
  - research/artifacts/search-degree4-five-corner-omega.py
  - research/artifacts/search-degree4-five-corner-omega.sbatch
---

Consider the two length-twelve degree-four sign classes

```text
-+-++-+-++++          -+-+++-+-+++
```

whose orbit profiles are `(1,1,5,5)` and whose two residual orbits each have
four singleton corners and one length-eight corner.  Across every injection
of the immutable packet `(r,e,a,c,b,d,p)` into twelve slots, with the other
five slots equal to one, neither choice of unary pivot makes the other unary
relation trivial.  Consequently no such layout realizes the ordered Omega
four-cycle or kills `Omega(c,p)`.

The exact count is

```text
2 * 12P7 = 7,983,360 layouts,
15,966,720 layout/pivot choices,
0 unary-compatible choices,
0 target hits.
```

This does not exclude repeated or composite coefficients, the other four
dihedral `(1,1,5,5)` classes with different corner-length profiles, or the
next equal-residual profile `(1,1,7,7)` at length sixteen.

