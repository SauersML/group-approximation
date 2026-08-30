---
rg: 2
id: rational-solvable-weinbaum-visibility-boundary-proof
kind: route
title: Take one finite rational-derived quotient or use functoriality to kill the residual
target: rational-solvable-weinbaum-visibility-boundary
requires: [linton-radical-has-a-short-weinbaum-marker]
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Suppose first that `S intersect R` is empty.  For each `s in S`, choose `n_s`
with `s notin G_Q^(n_s)`.  Finiteness of `S` lets us take
`N=max_s n_s`.  Then the quotient

    q_N:G -> G/G_Q^(N)

is nontrivial on every member of `S`.  Its finite normal series induced by

    G=G_Q^(0) >= G_Q^(1) >= ... >= G_Q^(N)

has torsion-free abelian factors.  Hence the quotient is solvable and amenable.
It is also locally indicable: if `L` is a nontrivial finitely generated
subgroup, choose the first layer of the series in which the image of `L` is
nontrivial.  That image is a nontrivial finitely generated subgroup of a
torsion-free abelian group, and therefore maps onto `Z`.  Restricting and
composing gives an epimorphism `L->Z`.  This proves (1) implies (3), while
(3) implies (2) is immediate.

Conversely let `phi:G->Q` with `Q` rationally solvable.  Functoriality gives

    phi(G_Q^(n)) <= Q_Q^(n)

for every `n`.  A finite rational-derived term of `Q` is trivial, so `phi(R)=1`.
Thus no map as in (2) can retain a member of `S intersect R`, proving (2)
implies (1).

For the final one-relator assertion, if `R=1` then the equivalence applies.
If `R` is nontrivial, the short-marker prerequisite supplies a member of the
Weinbaum packet in `R`, so the equivalence fails.  Any amenable locally
indicable image retaining the packet is consequently not rationally solvable.
If `R` is perfect, its image is perfect; a perfect subgroup of a solvable group
is both perfect and solvable and hence trivial.  Thus in this perfect-radical
subcase a packet-retaining image must be nonsolvable.
