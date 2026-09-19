---
rg: 2
id: mark-relative-finite-packet-decoder-is-impossible
kind: claim
title: A nonzero mark-relative BCS decoder cannot live in a finite or residually finite torsion packet
distinct_from:
  unconditional-bcs-ultraproduct-decoder-forces-ce: that refutes decoders defined on the trivial homomorphism; this permits all mark-dead maps and uses a mark-alive finite representation instead.
  reverse-kleene-unconditioned-collapse-forces-fd-invisibility: that derives finite-dimensional invisibility from an unconditional numerical mark cutoff; this derives it from a qualitative mark-relative BCS corner decoder and covers rational group-algebra marks.
  finite-packet-central-sign-cannot-enforce-nonlinear-support: that uses induction of selector characters to refute central-sign spectral pruning; this applies even to a selected primitive-type group-algebra projection.
---

Let `(B,D)` be a BCS signal for which every exact finite-dimensional strategy
kills `D` (in particular every Fanizza NONHALT instance).  Let `Gamma` be a
group and `0!=p in C[Gamma]`.  Suppose every matrix-ultraproduct homomorphism
`pi` with `pi(p)!=0` is claimed to decode a perfect finite-dimensional/CE BCS
state with positive `D` mass.

Then `p` must be killed by **every finite-dimensional representation** of
`Gamma`.  Indeed, a mark-alive finite-dimensional representation repeated as
a constant sequence is a matrix-ultraproduct homomorphism.  The decoder would
produce a perfect marked BCS state, contradicting exact NONHALT soundness.

Consequently no such nonzero mark-relative decoder can be based solely on:

1. one finite torsion, Pauli, Clifford, hyperoctahedral, or signed-permutation
   group packet;
2. a nonzero primitive central type projection in the group algebra of that
   packet;
3. any residually finite compiled group with a nonzero group-algebra mark.

For (3), residual finiteness separates the finite support of `p` in one finite
quotient, and the regular representation of that quotient detects `p`.

Thus allowing the trivial/mark-dead map removes the unconditional-decoder
obstruction but does **not** make a finite packet into the desired compiler.
A successful NONHALT group must already place its nonzero mark in the
finite-dimensional representation radical, and must then prove the stronger
matrix-ultraproduct death by a genuinely infinite matrix-only actuator.

The ordinary Fanizza reflection shadow exhibits the concrete escape.  Its
`S_4` stationary-overlap representation can be tensored with a mark-alive
`D_8` Pauli representation.  All reflection/central-sign group words remain
exact, the mark survives, and the additive overlap remains `1/4`.  Therefore
an independent finite Pauli authenticator does not turn the reflection shadow
into a native BCS corner.
