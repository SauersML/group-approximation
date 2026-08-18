---
rg: 2
id: weyl-algebra-blocks-a-universal-leavitt-host
kind: claim
title: The first Weyl algebra does not embed in the binary Leavitt algebra, so it is not a universal host
invalidates: [boone-higman-via-universal-leavitt-host]
distinct_from:
  augmentation-blocks-unital-leavitt-family: that shows an augmentation obstructs a unital binary Leavitt FAMILY inside a group algebra, so the Leavitt relations are the guest and the obstruction is an augmentation; this shows the first Weyl algebra is not a guest of L_K(1,2), the obstruction is the Heisenberg relation in Steinberg algebras, and the Leavitt algebra is the host.
  division-ring-hosts-no-binary-leavitt-family: that says a division ring cannot CONTAIN a binary Leavitt family -- the Leavitt algebra is the guest; this says the binary Leavitt algebra cannot contain the first Weyl algebra -- the Leavitt algebra is the host. The directions are opposite and neither implies the other.
  binary-leavitt-algebra-not-directly-finite: that is the failure of direct finiteness inside the binary Leavitt algebra, used here as an approximation obstruction; this is a nonembedding theorem about which algebras fit inside it, and its proof runs through Steinberg algebras rather than through any finiteness of modules.
  universal-leavitt-el4-nonsofic: that concerns nonsoficity of a rank-four elementary group over the universal Leavitt algebra; this concerns which K-algebras embed in the Leavitt algebra itself, with no group and no approximation property.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

The first Weyl algebra does not embed into the Leavitt algebra `L_K(1,2)`.

**Verification status.**  Read from source 2026-08-17.  Bilich--Hazrat--Nam,
*Embedding K-algebras into Leavitt algebra L_K(1,2)*, arXiv:2512.09241v2
(submitted 10 December 2025, revised 22 December 2025), abstract: "we show
that the Heisenberg equation $xy-yx=1$ cannot be realized in any Steinberg
algebra, implying that the first Weyl algebra cannot be embedded into
$L_K(1,2)$".  The same paper proves positive embedding results for Bergman
`K`-algebras and for Leavitt path algebras of finite graphs satisfying
condition (L).

## What it kills in this repository

This repository has invested heavily in `L_K(1,2)` and its elementary
groups — `GroupApproximation/Leavitt/UniversalLeavittOver.lean` presents it,
`FinitePresentation.lean` proves it finitely presented,
`LeavittSimplicity.lean` proves the strong form `x != 0 => exists a,b : axb =
1`, and `ElementaryPerfect.lean` and `ElementaryNoFiniteQuotients.lean`
develop the elementary groups.  That is a finitely presented, strongly simple
ring whose elementary groups have exactly the properties a Boone--Higman
envelope would want.

The tempting move is therefore to treat it as a universal host: embed the
group ring that `chatterji-kassabov-normal-generator-embedding` produces into
`L_K(1,2)` and inherit simplicity and finite presentation together.  This
claim refutes the general form of that move.  A blanket embedding theorem for
countable or finitely presented `K`-algebras into `L_K(1,2)` is false, and
the obstruction is not exotic — it is the Heisenberg relation, which no
Steinberg algebra realizes.

## What it does not kill

It does not say the group rings arising in the Boone--Higman construction
fail to embed.  Bilich--Hazrat--Nam's positive results show the class of
embeddable algebras is large.  A Leavitt route remains conceivable, but it
would need a theorem tailored to those particular group rings, and it could
not be obtained by citing a universal-host statement, because there is none.
