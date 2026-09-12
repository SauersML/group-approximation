---
rg: 2
id: atlas-o8p2-ten-marked-packet-collision-screen-proof
kind: route
title: Replay ten O8+(2) marked conjugator fibers using class multiplication
target: atlas-o8p2-ten-marked-packet-collision-screens-are-empty
requires:
  - atlas-o8p2-cross-class-pairs-reduce-to-ten-marked-screens
  - atlas-shortest-a4-triangle-packet
  - atlas-word-19243-is-kernel-relation
artifacts:
  - experiments/atlas_o8p2_ten_packet_screens.py
  - experiments/atlas-o8p2-ten-packet-screens.json
---

The replay reconstructs `G=PrimitiveGroup(135,2)`, its three affine
`2^6:A8` triality carriers, and both complement classes in each carrier.  It
then identifies the three natural and three orthogonal ambient classes by
exact conjugacy with the `A9` and `S6(2)` carrier charts.  Each chart is
identified with `GL4(2)`.  Relative graph parity is the contragredient map

```text
M |--> (M^-1)^T.                                      (O8R1)
```

The thirty packet words are reduced only by their factor-oriented ordered
pairs, leaving sixteen distinct directed edges.  The erroneous twelve-edge
order-role collapse is not used.

For a seed edge `(x,y)`, let `C_i,C_j` be the ambient conjugacy classes of
`x,y`.  If `c_ijk` is the character-table class multiplication coefficient,
then the number of `y' in C_j` for which `(xy')^3=1` is exactly

```text
sum_{ord(C_k) in {1,3}} c_ijk |C_k| / |C_i|.          (O8R2)
```

Multiplying `(O8R2)` by `|C_G(y)|` counts the conjugator fiber.  The script
uses `(O8R2)` to choose the smallest of the sixteen seed fibers.  It then
replays that fiber explicitly: for every compatible `y'`, choose
`g0` with `y^g0=y'` and enumerate `c g0` for all `c in C_G(y)`.  This is every
ambient conjugator satisfying the seed exactly once.  An internal assertion
checks that the explicit count equals the independently computed
class-multiplication count.

The remaining fifteen packet edges and the literal decoded collision word are
then multiplied in `G`.  Assertion-hardened totals are `(O8S1)` and `(O8S2)`;
all ten packet-plus-collision counts are zero.  The validated replay used Sage
10.7 on one Milan CPU per Sioux node; no floating point, sampling, or
174,182,400-element ambient loop is involved.

