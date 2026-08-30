---
rg: 2
id: whitehead-vanishing-recursively-presented-torsion-free
kind: claim
title: Whitehead vanishing for finitely generated recursively presented torsion-free groups
distinct_from:
  whitehead-vanishing-torsion-free: that quantifies over all torsion-free groups; this quantifies over a countable presentation class, and the established finite-support route shows the two are equivalent.
  whitehead-vanishing-finitely-presented-torsion-free: that demands finite presentation; the established Whitehead-injective Higman embedding now proves the two claims equivalent.
  torsion-free-universal-quotient-recursively-presented: that is the effective construction of torsion-free quotients used by the global reduction; this is the still-open Whitehead vanishing statement for the groups produced.
  whitehead-injective-torsion-free-embedding: that is the now-established transfer theorem; this node is the vanishing statement it transfers.
  torsion-free-finitely-presented-non-mf: that asks for an approximation-theoretic counterexample; this is an unrelated algebraic K-theory conjecture.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Wh(K)=0 for every finitely generated recursively presented torsion-free
group K.

**OPEN, but now exactly equivalent to both the finitely presented and global
torsion-free cases.**

The upward transfer is complete: the route
[[whitehead-recursively-presented-via-injective-embedding]] embeds K in a
finitely presented torsion-free H with Wh(K)->Wh(H) injective. Thus the
finitely presented vanishing claim implies this one.

The downward-to-global reduction was already complete. Given a Whitehead
class over an arbitrary torsion-free G, record the finite multiplication
table supporting a matrix and its inverse, form a finitely presented group P,
and pass to its recursively presented universal torsion-free quotient P^tf.
The comparison map P^tf->G points in the functorially useful direction, so
vanishing for P^tf kills the original class. This is
[[whitehead-global-via-recursively-presented-reduction]].

No inequation apparatus is needed. The only unresolved input is now the
actual vanishing for finitely presented torsion-free groups, equivalently
Wh(U)=0 for the single tester U from
[[whitehead-universal-finitely-presented-torsion-free-group]].
