---
rg: 2
id: hnn-reduced-word-transfer-to-subgroup-extension
kind: claim
title: Reduced words transfer between an HNN extension of a subgroup and the ambient one
artifacts:
  - GroupApproximation/Computability/BooneGroupTower.lean
---

ESTABLISHED (2026-08-16).  This was the only unproved part of Simpson's
good-subgroup lemma, and it is now `mem_toSubgroup_subOne_iff`, `pushWord` and
`smallLift_prod` in `Computability/BooneGroupTower`.

Let `A <= G` with `phi : Asub =~ Bsub`, and suppose `A` is *good*: `phi` carries
`A cap Asub` onto `A cap Bsub`.  Set `A1 = Asub.comap A.subtype` and
`B1 = Bsub.comap A.subtype`, subgroups of `A`, so that goodness restricts `phi`
to `phi1 : A1 =~ B1`, and let

    psi = HNNExtension.lift (of . A.subtype) t hx
        : HNNExtension A A1 B1 phi1 ->* HNNExtension G Asub Bsub phi.

What is needed:

1. a word over `A` is reduced in the small extension exactly when its image is
   reduced in the big one -- the `chain` field of `ReducedWord` transfers
   letter by letter; and
2. the compatibility `psi (w.prod phi1) = (pushforward w).prod phi`.

Both are structural.  The reason (1) holds with nothing to prove
mathematically is that for a letter `a` *of `A`*,

    (a : G) in Asub  <->  a in A1

by the definition of `A1` as a comap.

## Why this is the right shape of hole

It replaces the ledger's earlier plan -- "turn an arbitrary word
`a0 t^{e1} a1 ... t^{en} an` into a reduced one, pinching with `phi`, by strong
induction on `n`" -- with a statement containing no induction and no word
surgery.  The pinch step that induction needed is already proved
(`good_pinch`, `good_pinch_inv`); what the induction was really doing was
re-deriving the transfer above one letter at a time.

Estimated cost: the two items are the transfer of a structure field and one
`MonoidHom` computation on a normal form.

Both items landed in `a44616f4`, and [[hnn-good-subgroup-lemma]] closed with
them in the same commit.  The estimate above was right about the shape and the
size: no induction on stable letters appears anywhere in the finished proof.
