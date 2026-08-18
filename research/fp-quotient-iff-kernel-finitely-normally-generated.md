---
rg: 2
id: fp-quotient-iff-kernel-finitely-normally-generated
kind: claim
title: A quotient of a finitely presented group is finitely presented exactly when the kernel is finitely normally generated
invalidates: [boone-higman-via-maximal-quotient-of-the-envelope]
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that characterizes finite presentability of a twisted Brin-Thompson group in terms of an ACTION -- orbits of pairs and point stabilizers; this characterizes finite presentability of a QUOTIENT in terms of its kernel's normal generating data, and no action appears in it.
  boone-final-group-finitely-presented: that establishes that one particular group is finitely presented; this is a general equivalence relating finite presentability of any quotient of a finitely presented group to finite normal generation of its kernel.
  finitely-presented-nonsofic-group-exists: that is an existence statement combining finite presentation with failure of soficity; this is a presentation-theoretic equivalence with no approximation property in it.
  hnn-extension-finite-presentation-permanence: that is a permanence statement for one construction -- an HNN extension of a finitely presented base along finitely generated associated subgroups is finitely presented; this is the general kernel criterion for quotients, mentions no HNN extension, and is an equivalence rather than a one-way permanence.
  boone-normal-closure-of-t-finitely-generated: that says a normal closure in the Boone tower becomes finitely generated AS A SUBGROUP after finitely many stages; this is about finite normal generation in the ambient group, which is a strictly weaker condition on a strictly different object, and conflating the two is the specific error this node exists to prevent.
  common-quotient-onto-normal-subgroup: that constructs a common quotient mapping onto a prescribed normal subgroup; this states no construction and only relates finite presentability of a quotient to finiteness of normal generating data for its kernel.
artifacts:
  - GroupApproximation/Algebra/FinitePresentationKernel.lean
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `Gamma` be finitely presented and `N <| Gamma`.  Then

    Gamma/N  finitely presented
      <==>
    N  finitely normally generated in  Gamma .

The forward direction is formalized in this repository, in
`GroupApproximation/Algebra/FinitePresentationKernel.lean`:

    theorem ker_isFinitelyNormallyGenerated {E : Type u} [Group E] {W : Type v}
        [hE : Group.IsFinitelyPresented E] [Group.IsFinitelyPresented W]
        (f : E →* W) (hf : Function.Surjective f) :
        f.ker.IsFinitelyNormallyGenerated

The reverse direction is one Tietze move: adjoin finitely many normal
generators as relators.

## Why this is the pivot of the whole Boone-Higman region

`proper-normal-subgroups-miss-the-normally-generating-core` delivers, for
every finitely generated group with solvable word problem, a finitely
presented envelope every one of whose maximal proper normal quotients is
simple and still contains the group.  This claim says the one remaining
requirement — finite presentability of that quotient — is not merely implied
by finite normal generation of the kernel but **equivalent** to it.

So the gap is not a bookkeeping step that a cleverer Tietze argument might
absorb.  It is a genuine property of the normal lattice, and any proof of
`boone-higman-conjecture` through this envelope has to establish it.  The
equivalence is also what lets the graph state the target as a property of a
subgroup (`ck-envelope-has-a-finitely-normally-generated-maximal-kernel`)
rather than of a quotient, which is the form the repository's Lean
infrastructure can address.

## The error it kills

"A quotient of a finitely presented group is finitely presented" is false.
For any finitely generated `Q` that is not finitely presented, a surjection
`F_k ->> Q` from a finitely generated free group has finitely presented
source and non-finitely-presented target; equivalently its kernel is not
finitely normally generated.  Zorn's lemma produces a maximal normal
subgroup and supplies no finite normal generating set with it, so the
four-step argument "build the envelope, take a maximal normal subgroup, the
quotient is simple, quotients of finitely presented groups are finitely
presented" fails at the last step and only there.  That argument is recorded
as `boone-higman-via-maximal-quotient-of-the-envelope` and
this claim is its invalidator.

## A distinction that costs people the argument

Finite normal generation of `N` in `Gamma` is much weaker than finite
generation of `N` as a group.  This repository already contains an example of
the gap in the other direction, `simple-lamp-radical-one-relation`, where an
infinitely generated radical is the normal closure of a single element.  The
Boone-tower results (`boone-normal-closure-of-t-finitely-generated`) prove
the *subgroup* form after finitely many HNN stages and are therefore not
usable here; see the `distinct_from` note above.
