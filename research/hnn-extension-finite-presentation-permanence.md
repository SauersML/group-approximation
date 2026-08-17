---
rg: 2
id: hnn-extension-finite-presentation-permanence
kind: claim
title: An HNN extension of a finitely presented group along finitely generated associated subgroups is finitely presented
distinct_from:
  literal-group-not-sofic: That is a claim about soficity of the manuscript's group E; this is a generic permanence statement for HNN extensions, with no approximation property and no particular group in it.
  mf-finite-normal-tracially-visible: That is about finite normal subgroups of an MF group and traces; this is about presentations of HNN extensions and mentions neither.
artifacts:
  - GroupApproximation/Computability/BooneGroupTower.lean
---

OPEN, and not in Mathlib in any form.  If `G` is finitely presented and
`Asub, Bsub <= G` are finitely generated with `phi : Asub =~ Bsub`, then
`HNNExtension G Asub Bsub phi` is finitely presented: add one generator `t` and
one relation `t a t^{-1} = phi a` for each of finitely many generators `a` of
`Asub`.

## Why it is a separate claim rather than a step

It is entirely generic -- no machine, no modular arithmetic, no free basis --
and it is the only missing ingredient of
[[boone-final-group-finitely-presented]] that is *about HNN extensions in
general* rather than about the Boone tower.  Anything else in the repository
that builds a group as an HNN extension and needs finite presentability wants
the same statement, so it is worth having as a node rather than inline.

Mathlib has `HNNExtension` with its normal form and Britton's Lemma, and has
`PresentedGroup`, but nothing connecting the two in this direction.  The proof
is a presentation manipulation: exhibit the obvious surjection from the
presented group onto the extension and use the normal form to show it is
injective.
