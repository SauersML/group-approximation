---
rg: 2
id: grigorchuk-hnn-tree-stabilizers-not-fp2
kind: claim
title: Every action of Grigorchuk's HNN extension on a tree without a global fixed point has a vertex stabilizer that is not finitely presented and not of type FP_2
distinct_from:
  grigorchuk-hnn-extension-is-fp-infinity: that asks whether the extension is of type FP_infinity and notes that Brown's criterion fails on its own Bass-Serre tree; this kills Brown's criterion on every tree the group acts on, including every other splitting and every change of base.
  grigorchuk-hnn-has-no-base-first-wreath-rewriting-system: that kills one class of rewriting-system certificates; this kills the tree-action (Bass-Serre / Mayer-Vietoris) certificates, by the same subgroup-commensurability input.
---

**ESTABLISHED (obstruction to a family of certificates).** Proof:
`grigorchuk-hnn-tree-stabilizers-not-fp2-proof`.

Let `𝔊^` be Grigorchuk's finitely presented ascending HNN extension of the first Grigorchuk group
`𝔊` (`grigorchuk-hnn-extension-is-fp-amenable-non-ea`), with stable letter `t`, character
`χ : 𝔊^ → Z` and kernel `N = ⋃_n t^n 𝔊 t^(−n)`.

**Statement.** Let `𝔊^` act on a tree `T` without inversions and without a global fixed vertex.
Then:

1. every vertex stabilizer lies in `N`;
2. every vertex stabilizer is either finite or **not finitely presented**;
3. `𝔊` fixes a vertex, and the stabilizer of every vertex fixed by `𝔊` is infinite and not
   finitely presented;
4. with the recalled theorem that the Schur multiplier `H_2(𝔊; Z)` is an infinite elementary
   abelian 2-group (Grigorchuk 1999), items 2 and 3 also hold with "not of type `FP_2` over `Z` or
   over `F_2`" in place of "not finitely presented".

**Consequence for Zaremsky 1.12.** Brown's criterion on a tree proves `FP_n` for `n ≥ 2` only if
all vertex stabilizers are `FP_n`. So no action on a tree, and no graph-of-groups decomposition of
`𝔊^` (any splitting, any other ascending base `B' ≤ N`, any other stable letter), certifies even
`FP_2`, although `𝔊^` is finitely presented. A certificate of `FP_3` or `FP_∞` for `𝔊^` must come
from a contractible complex of dimension at least 2 (where the torsion group `𝔊` need not fix a
cell), from a direct resolution, or from a non-geometric method. Together with the Kropholler fence recorded in
`grigorchuk-hnn-extension-is-fp-infinity` (no finite-dimensional complex with `H𝔉` stabilizers),
this removes every Bass–Serre-type route.

**The step where these certificates fail.** A finitely generated vertex stabilizer inside `N`
lies in a single conjugate of `𝔊`. By Grigorchuk–Wilson it is finite or commensurable with `𝔊`,
hence finite or not finitely presented. But `𝔊` is a finitely generated torsion group, so it fixes a
vertex, and that vertex has an infinite stabilizer. Item 1 is where the torsion of `N` enters: it
forces the stable letter, and every element outside `N`, to act hyperbolically.

**Calibration.** For `BS(1,2) = Z*_(×2)` the Bass–Serre tree has vertex stabilizers `Z`, of type
`FP_∞`. Both inputs fail there: `N = Z[1/2]` is not torsion, and it contains
the infinite finitely presented subgroup `Z`.

**Scope.** It does not apply to the Basilica extension, whose kernel contains `Z^n`
(`basilica-hnn-extension-is-fp-infinity`). It says nothing about contractible complexes of dimension `≥ 2`.
