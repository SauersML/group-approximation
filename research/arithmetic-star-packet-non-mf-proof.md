---
rg: 2
id: arithmetic-star-packet-non-mf-proof
kind: route
title: Attach S9 to the eight compression cosets and apply finite-packet collapse
target: arithmetic-star-packet-non-mf
requires:
  - affine-congruence-source-is-kazhdan
  - finite-noncommutative-packet-compression-collapse
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceKazhdan.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceTorsionFree.lean
---

Let `H=alpha(P)` and `X=P/H`; the certified doubling source has `[P:H]=8`.
`P` acts transitively on `X`.  In `F=Sym(X union {star})`, the star
transposition `k=(H star)` is fixed by its point stabilizer `H`; the omitted
element `p_0` sends it to the distinct transposition `(p_0 H star)`.  Thus
`[p_0,k]!=1` in `F rtimes P`.

Amalgamate `F rtimes P` with the ascending HNN envelope along `P`.  Normal
form injects each factor, so the mark remains nontrivial.  In the HNN factor
the stable letter compresses `P` onto `H`, while in the packet factor `P`
normalizes the finite group `F` and `H` fixes `k`.  The finite-packet collapse
therefore kills the mark in every norm matrix corona.

Finite presentation is obtained from finite presentations of the two factors
by adding one identification relation for each member of a finite generating
set of `P`.
