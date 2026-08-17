---
rg: 2
id: torsion-free-higman-embedding
kind: claim
title: Torsion-free Higman embedding
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Every recursively presented torsion-free group embeds into a finitely
presented torsion-free group.

**ESTABLISHED 2026-08-17** from Chiodo, arXiv:1107.1489v4, Theorem 2.2, read
and quoted from source; see `torsion-free-higman-embedding-via-chiodo-torsion-orders`.
That theorem gives a uniform algorithm sending a countably generated
recursive presentation `P` to a finite presentation `T(P)` with
`P- ↪ T(P)` and `Tord(P-) = Tord(T(P))`, where `Tord` is the set of orders
of nontrivial torsion elements.  Empty torsion-order set in, empty
torsion-order set out.  Chiodo attributes the theorem to his own earlier
work ([4, Lemma 6.9 and Theorem 6.10] in his numbering) and notes it is
implicit in Rotman's proof of Higman embedding (Theorem 12.18) -- which
matches the informal reason this node
previously recorded, that torsion in an HNN extension is conjugate into the
base and torsion in an amalgam into a factor.

## History of this node, kept deliberately

It stood open for months with the status "literature-plausible, not verified
at theorem level", on the strength of a *weaker* neighbouring result:
Chiodo--Hill (arXiv:1610.00977) preserve torsion orders when embedding a
**finitely presented** group into an 8-generator 26-relator one, which is
finitely-presented-to-finitely-presented and does not give this claim.  The
node also refused to lean on Belegradek, cited in the secondary literature
but unread.  Both cautions were correct; what was missing was simply that the
recursively-presented form is Theorem 2.2 of a paper already cited here for
other purposes.  The lesson is narrow and worth keeping: a citation checked
at *usage* level (Fournier-Facio uses the universal-group form) can leave the
stronger, directly applicable theorem in the same literature unread.

## Neighbouring statements, all now read

* Chiodo Theorem 3.9: one finitely presented torsion-free group containing
  every countably generated recursively presentable torsion-free group --
  strictly stronger than the payload formalized in
  `GroupApproximation/Monsters/UniversalFinitelyPresentedTorsionFreeGroup.lean`,
  which absorbs finitely presented torsion-free groups only.
* Chiodo Theorem 3.10 (= Belegradek, appendix to [1], Theorem A.1): the
  universal finitely presented torsion-free group.  This is the form
  Fournier-Facio uses as the first input of arXiv:2608.02025 Section 2.
* `torsion-free-universal-quotient-recursively-presented`: the effective
  torsion-free radical quotient from the same paper, used alongside this
  claim by `finite-pattern-realization-via-torsion-free-radical`.

## What it does not give

An embedding, and nothing else.  It says nothing about `K_1`, and in
particular does not make `Wh(K) -> Wh(H)` injective; that gap is
`whitehead-injective-torsion-free-embedding`.  Routes may now depend on this
claim without inheriting an unverified premise, but must not silently upgrade
"embeds" to "embeds with control on an invariant".
