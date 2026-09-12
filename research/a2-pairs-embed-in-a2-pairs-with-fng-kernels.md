---
rg: 2
id: a2-pairs-embed-in-a2-pairs-with-fng-kernels
kind: claim
title: Every type [A_2] pair sharply embeds in a type [A_2] pair whose kernel is finitely normally generated
distinct_from:
  permutational-boone-higman-conjecture: that asks every decidable group to embed in a faithful type (A) actor; this asks that the kernel of any given type [A_2] actor can be removed by a sharp embedding, which together with Boone--Higman would give that conjecture.
  fp-simple-groups-embed-in-fp-simple-mif-groups: that is BFFHZ Question 3.4, removing mixed identities by enlarging a finitely presented simple group; this is FFWZ Question 5.9, removing an action kernel by enlarging a type [A_2] pair.
  a2-kernel-removal-forces-recursive-kernel: that proves a recursive kernel is necessary for one pair; this is the universal assertion.
  a2-action-with-non-finitely-presented-image: that is one pair whose image is not finitely presented but whose kernel is removable; this asserts removability for every pair.
artifacts:
  - research/artifacts/bh-type-a-actions-2026-09-12.md
---

**OPEN.** This is the first part of Fournier-Facio--Wu--Zaremsky,
arXiv:2603.24687v2, Question 5.9, read from the PDF text on MSI:

> "For G ↷ S an action of type [A_2] with kernel K, does there always exist an
> action G′ ↷ S′ of type [A_2] with kernel K′ finitely normally generated, such
> that (G,K) sharply embeds in (G′,K′)?"

Their note: "a 'yes' answer to the first part of Question 5.9 would tell us that
(relPBH) implies (PBH)". With their Theorem C
(`boone-higman-implies-relative-permutational-bh`), (BH), (relPBH) and (PBH)
would then all be equivalent. The graph carries this as the route
`pbh-via-bh-and-a2-kernel-removal` into `permutational-boone-higman-conjecture`.

## Attempts

1. **Normalizer covers.** Extend a type (A) actor `Γ` by a free group acting
   through a normalizing subgroup `Q`, as in
   `normalizer-extension-of-type-a-actor-is-a2-cover`. The kernel is removable
   whenever `Q` lies in a finitely presented group `P` of normalizing
   permutations with `P ∩ Γ = 1`: embed in `Γ x| (F_m * P)`. The explicit
   example `a2-action-with-non-finitely-presented-image` has a non-finitely-
   presented image, with `Q = δ(Z wr Z)` inside `P = δ(V)`. Its kernel is
   removed this way. *Dies* as a counterexample source: failure of finite
   presentation of the image does not by itself obstruct removal. Covers whose
   `Q` lies in no such `P` were not examined.
2. **Computability.** `a2-kernel-removal-forces-recursive-kernel` shows a
   removable kernel is recursive. For the FFWZ Theorem C actor of a finitely
   presented simple group `Γ`, recursiveness of the kernel implies
   recursiveness of the one-variable mixed identities of `Γ`. So an infinite
   finitely presented simple group with a non-recursive set of mixed identities
   would refute this claim. *Deferred*: no such group is known here, and
   producing one needs a simple group whose mixed identities encode a
   non-r.e. set while the group stays finitely presented.
3. **Remove mixed identities instead.** For the Theorem C actor, an element of
   the kernel sends each `x_i` to `x_i` times a mixed identity (BFFHZ, the
   non-MIF discussion after Lemma 2.2). An MIF overgroup of `Γ` makes the actor
   faithful. That is BFFHZ Question 3.4
   (`fp-simple-groups-embed-in-fp-simple-mif-groups`), also open, so this only
   trades one open question for another.
