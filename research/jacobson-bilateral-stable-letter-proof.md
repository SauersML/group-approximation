---
rg: 2
id: jacobson-bilateral-stable-letter-proof
kind: route
title: Verify seven substitutions on the bilateral basis and conjugate the full finite boundary packet
target: jacobson-stable-letter-closes-boundary-recursion
requires:
  - jacobson-full-boundary-forces-six-coordinate-packet
  - jacobson-full-boundary-packets-have-compatible-regular-models
artifacts:
  - research/artifacts/jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md
---

The prerequisites specify `B,C`, their entire intersection, and the
elements `tau(g),delta(g),h_0,h_1`. The finite set
`{x_13,x_31,w_23}` generates the three-dimensional general linear
group, so its six head/tail conjugation equations imply the same
equations for every element of the original finite packet.

On the bilateral vector space over `F_2`, extend every original
operator by the identity at negative levels. Translation of every
level by one sends the head action to `tau(G)`, the original tail
to `delta(G)`, and the original staggered involution to `h_1`.
It therefore satisfies all seven new relations while leaving the
original head transvection nonidentity. Restriction to each finite
packet is still its faithful literal representation.

Conjugating the old boundary identity by the one new stable letter
gives the missing recursive boundary identity with all operators
defined by the same words. Conjugating the entire finite table gives
the whole next boundary packet. Iteration proves exact recursive
closure. This is a group-presentation statement and supplies no
dimension-independent lower bound for unitary matrix errors.
