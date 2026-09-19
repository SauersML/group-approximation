---
rg: 2
id: whitehead-vanishing-recursively-presented-torsion-free
kind: claim
title: Whitehead vanishing for finitely generated recursively presented torsion-free groups
distinct_from:
  whitehead-vanishing-torsion-free: that quantifies over all torsion-free groups, of which there are continuum many finitely generated ones; this quantifies over the countable class of recursively presented ones. The reduction from that to this is a theorem (audit Section C), not a restatement.
  whitehead-vanishing-finitely-presented-torsion-free: that demands finite presentation; this only recursive presentation, and the gap between them is precisely whitehead-injective-torsion-free-embedding. Chiodo Theorem 2.2 bridges the two as *groups* but says nothing about Wh.
  torsion-free-universal-quotient-recursively-presented: that is the construction of a recursively presented torsion-free quotient, a tool with no K-theory in it; this is a Whitehead vanishing statement quantified over the class that tool produces. That claim is established and this one is open.
  hnn-torsion-theorem: that claim is about torsion-freeness passing from an HNN base to the extension; this is about K_1 of integral group rings of groups already assumed torsion-free. Neither mentions the other's subject matter.
  torsion-free-finitely-presented-non-mf: that asserts one finitely presented torsion-free group fails MF; this asserts every finitely generated recursively presented torsion-free group has vanishing Whitehead group. Different quantifier, different class, and no approximation property appears here.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

`Wh(K) = 0` for every finitely generated recursively presented torsion-free
group `K`.

**This suffices for the global conjecture.**  That is sharper than the
obvious reduction to finitely generated groups, and it is not obvious: there
are continuum many finitely generated torsion-free groups and only countably
many recursive presentations, so a statement quantified over recursively
presented groups looks a priori too weak.  It is not, because the *class* of
a matrix transplants even when the group does not: build the finitely
presented group `P` on the finite multiplication table of the coefficients of
`A` and `A^-1`, pass to its torsion-free universal quotient `Ptf`
(`torsion-free-universal-quotient-recursively-presented`), and observe that
the comparison homomorphism `Ptf -> G` points the *right* way, so plain
functoriality carries the vanishing back.  Proof in audit Section C.

Two consequences worth keeping:

* No inequation apparatus is needed for this step.  Sets of nontrivial
  differences are needed only when the target is a finitely *presented*
  overgroup, where the comparison map points the wrong way and faithfulness
  has to be bought; that is `finite-torsion-free-pattern-realizable-finitely-presented`.
* Because this reduction lands exactly on the class over which the natural
  repair of the finitely-presented route is quantified, that repair
  (`whitehead-injective-torsion-free-embedding`) really would close the
  conjecture, rather than closing a proper sub-case.

## Attempts

**Push up to finitely presented groups.**  The live route:
`whitehead-recursively-presented-via-injective-embedding` reduces this to
`whitehead-vanishing-finitely-presented-torsion-free` plus injectivity of
`Wh(K) -> Wh(H)` along Chiodo's embedding.  *Dies* at the injectivity, which
no construction supplies -- see
`whitehead-injective-torsion-free-embedding` for why the two obvious repairs
(retraction, pattern transplantation) both fail.

**Use the recursive presentation itself.**  The hypothesis is a computability
condition, and the temptation is to enumerate relators and induct.  *Dies*
because `K_1(ZK)` is not built from a presentation in any effective way: a
recursive presentation bounds how the group is *described*, not how its
invertible matrices factor, and there is no known theorem converting an
enumeration of relators into control on elementary factorizations.  The
recursiveness in this claim is inherited from the reduction that produced the
class, not a resource the claim knows how to spend.
