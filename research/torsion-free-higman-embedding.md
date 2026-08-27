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

## Formalization state, 2026-08-19

This claim is now the *only* thing standing between this repository and
Chiodo Theorem 3.10, and it is carried in Lean as
`GroupApproximation.ChiodoHost.TorsionFreeHigmanHull`, evaluated at one
explicit group.

What is proved unconditionally, and needs nothing from this node:

* Chiodo §3 entire --- `Algebra/TorsionFreeRadical.lean` (the torsion-free
  radical as the infimum of the normal *isolated* subgroups, with Corollary
  3.4), `Algebra/TorsionFreeRadicalTower.lean` (Definition 3.1's tower, Lemma
  3.2, Proposition 3.3), `Algebra/TorsionFreeQuotient.lean` (the universal
  torsion-free quotient, its lift, uniqueness of the lift, and the retraction
  principle);
* `Monsters/ChiodoTorsionFreeAbsorber.lean` --- the group Theorem 2.2 has to
  be applied to: the restricted direct product of the groups of **all**
  finite presentation codes, passed to its universal torsion-free quotient.
  Countable, torsion-free, nontrivial, and containing a copy of every
  finitely presented torsion-free group;
* Chiodo Definition 2.1 and the empty-`Tord`-means-torsion-free step ---
  `Sofic/ChiodoUniversalHost.lean`, which also derives
  `FournierFacioUniversal.UniversalTorsionFreeHost` from a hull for that
  group.

What this node still owes: the embedding itself, which is Higman's theorem
with the torsion orders controlled.  Note the index set.  The repository's
earlier payload
(`Monsters/UniversalFinitelyPresentedTorsionFreeGroup.lean`) was indexed by
the codes whose group is torsion-free, which is undecidable by Adian--Rabin,
so this claim could not be applied to it at all; the absorber replaces that
filtering by a torsion-free quotient, which is Chiodo's own Proposition 3.8
device, and the index set is the full code type.  The claim is therefore now
*applicable* where before it was not, which is a different thing from being
proved.

### Update, later the same day

Higman's Lemma 3.2 --- benign subgroups are closed under intersections and
joins --- is now **proved** in Lean, together with the preimage half of his
Lemma 3.3, the finite presentation of amalgams over finitely generated
subgroups, and the pinch lemma the join rests on.  See
`notes/HIGMAN_BENIGN_LANE.md`.  The claim of this node is unaffected: what is
formalized is the first section of the standard proof, not the theorem.
