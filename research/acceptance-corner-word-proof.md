---
rg: 2
id: acceptance-corner-word-proof
kind: route
title: Expand the controlled acceptance block on the zero-control corner
target: acceptance-return-is-one-corner-word
requires: []
---

All control projections commute with `P_0` and `Q`.  On the zero-control
sector the controlled block unitary restricts to the prescribed verifier
acceptance block, while every other control block is orthogonal to `P_0`.
Compression on both sides by `P_0Q` therefore deletes every off-sector term.
The surviving operator is precisely `P_0Q(W_game-1)P_0Q`.  Taking its tracial
Hilbert--Schmidt square gives the remaining return moment; all possible cross
terms vanish by orthogonality of the block supports.
