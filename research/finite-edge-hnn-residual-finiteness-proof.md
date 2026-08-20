---
rg: 2
id: finite-edge-hnn-residual-finiteness-proof
kind: route
title: Preserve a Britton-reduced word in an HNN extension of a finite quotient
target: finite-edge-hnn-closures-cannot-finish-the-nonce-atlas
requires:
  - cycle-closure-cannot-remain-in-the-join-tree-group
  - finite-character-idempotents-have-exact-hnn-transport
---

It is enough to prove one HNN step.  Let `G` be residually finite, let
`A,B<=G` be finite, and let `phi:A -> B` be an isomorphism.  Consider a
nontrivial Britton-reduced word in the HNN extension.  Only finitely many base
syllables occur.  Residual finiteness supplies a finite quotient `pi:G -> Q`
which is injective on `A union B` and which keeps every syllable that is not
in `A` or `B` outside the corresponding subgroup image: for each forbidden
membership, separate the finitely many elements `g a^(-1)` or `g b^(-1)`
from the identity and intersect the resulting finite-index normal kernels.

The map `pi` induces an isomorphism `pi(A) -> pi(B)` and hence a homomorphism
to the HNN extension of the finite group `Q` along those finite subgroups.
The chosen word remains Britton reduced there, so it remains nontrivial.
That target is the fundamental group of a finite graph of finite groups; it
is virtually free and therefore residually finite.  A further finite quotient
separates the image of the word.  Thus the original HNN extension is
residually finite.

Finite induction proves the assertion for any finite sequence of such HNN
steps.  Applying `cycle-closure-cannot-remain-in-the-join-tree-group` to the
resulting hyperlinear group excludes a completed no-CE atlas.
