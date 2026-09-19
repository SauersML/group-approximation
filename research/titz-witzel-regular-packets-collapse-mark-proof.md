---
rg: 2
id: titz-witzel-regular-packets-collapse-mark-proof
kind: route
title: Charge each marked regular packet to a whole failed relator half-packet
target: titz-witzel-regular-packets-collapse-mark
requires:
  - titz-witzel-c2-cocycle-system
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Every component word in `(TWC3)--(TWC6)` restricts on `F_j` to left
translation by the corresponding ordered word in `p_j,q_j`.  Such a
translation fixes all of `F_j` if its voltage is the identity and fixes no
point otherwise.  The identical dichotomy holds for a free finite-group
action.

Call a packet marked when `u^8` is nontrivial on it.  By `(TWC6)`, its two
component voltages are conjugate, so a marked packet contributes all
`2|F_j|` of its points to the support of `u^8`.

If all eight component voltages in the four lines of `(TWC5)` were trivial
on this packet, the restrictions of `e,u` to `F_j times C2` would be an
exact finite action of the presented Titz--Witzel group.  Its simple
index-two subgroup `K` is infinite.  The restriction to `K` of any finite
action has kernel normal in `K`; simplicity makes that kernel trivial or
all of `K`, and injectivity into a finite symmetric group is impossible.
Thus every finite action kills `K`.  The parity assignment sending both
`e,u` to the nontrivial element is a quotient onto `C2`; its kernel contains
the finite residual `K`, and both have index two, so that kernel is exactly
`K`.  In particular `u^8` belongs to `K` and must act trivially.  This
contradicts the packet being marked.  Hence at least one of the eight
relator-component voltages is nonidentity.

That component moves an entire half-packet of `|F_j|` points.  Therefore,
if `w_j=2|F_j|/|Omega|` is the normalized weight of packet `j`, its
contribution to the sum of the four global relator defects is at least
`w_j/2`, whereas its contribution to `mu` is exactly `w_j`.  Summing this
inequality over the marked packets gives `(TWR1)`.  Unmarked packets make no
contribution to its left side, completing the proof.
