---
rg: 2
id: mixed-central-router-adjoins-without-collapsing-packet-proof
kind: route
title: Amalgamate only the relative pair, then induce the exact marked representation
target: mixed-central-router-adjoins-without-collapsing-packet
requires:
  - every-forbidden-atom-has-fixed-schur-pauli-words
  - mixed-central-cnot-completes-relative-rank-one-router
---

The fixed Schur words `a,b` are involutions and their commutator is a central
involution word in the class-two packet.  Therefore the subgroup
`H=<a,b,K,J>` maps identically into the packet and router vertex groups.
The normal-form theorem for free products with amalgamation injects both
vertices into `(MCA1)`.  The router map is an automorphism of its finite vertex
group, so the HNN normal-form theorem injects `(MCA1)` into the final group.

Given a representation of `P`, first induce it from `P` to `(MCA1)` and then
induce again to the HNN extension.  The original representation occurs in the
restriction.  Since `J` is central and acts as `-I` before induction, it acts
as `-I` on every induced coset copy.  This proves both packet survival and
nontriviality of the marked sign.

On a forbidden atom, `every-forbidden-atom-has-fixed-schur-pauli-words` gives
`[a,b]=-1`, while on a commuting relative sector it gives `[a,b]=+1`.
Substitution into the exact router rank and trace formulas proves the two
sector statements.  No selector-center amalgamation is used.
