---
rg: 2
id: rich-2to1-via-branch-selector-on-proved-2to1-instances
kind: route
title: Orient the proved 2-to-1 instances by an efficient branch selector, lift to a unique game, and right-merge to full richness
target: rich-2to1-games-conjecture
requires: [two-to-two-games-theorem, orientation-lifts-sandwich-2to1-game-values, efficient-branch-selector-on-proved-2to1-instances]
---

**Decomposition.** The Rich 2-to-1 Conjecture splits into three prerequisites.

| Prerequisite | Supplies | Status |
|---|---|---|
| `two-to-two-games-theorem` (2-to-1 form) | soundness `eta` on a fixed family `R_eta` | ESTABLISHED, by citation |
| `orientation-lifts-sandwich-2to1-game-values` | richness, and transfer of soundness through the lift and `Psi` | ESTABLISHED, new |
| `efficient-branch-selector-on-proved-2to1-instances` | completeness `1 - eta'` of the lift | OPEN |

The pairing-law hypotheses (entropy, `t`-wise uniformity, smoothness, finite
moments) contribute **no** prerequisite on this route, because `Psi` outputs
uniform laws. The only open content is a branch statistic: the minority-branch
mass at right vertices of YES labellings (sandwich item 3).

**Proof of the implication.** Fix `eps > 0`. Choose `eta <= eps/2` with
`eta'(eta) <= eps`, which is possible since `eta' -> 0`. Let `o` be the selector
for `R_eta`. Map an input `x` to `H(x) = Psi(U_o(R_eta(x)))`. Every stage is
polynomial time: `R_eta` by the imported theorem, `o` by the open claim, and
`U_o` and `Psi` by sandwich items (1) and (2), since the alphabet is a constant.

* YES: `val(H(x)) >= val(U_o(R_eta(x))) >= 1 - eta'(eta) >= 1 - eps`, by the
  selector claim and sandwich item (2).
* NO: `val(R_eta(x)) <= eta` by the imported theorem, so
  `val(H(x)) <= 2 val(U_o) <= 2 val(R_eta(x)) <= 2 eta <= eps`, by sandwich items
  (1) and (2).
* Richness: sandwich item (2).

So `Gap-Rich-2-to-1[1 - eps, eps]` is NP-hard for every `eps`. `square`

**How each prerequisite can fail.**

* The selector claim can fail for these instances while UGC holds through a
  different outer construction. Consequence (b) of the sandwich shows the
  existential version, over all reductions, is equivalent to the target. So
  pinning the family is what makes this a strictly separate hole.
* The two established prerequisites could have failed. The sandwich needs the
  right bit to be free per right vertex; for a lift that also merged right
  vertices, item (1) breaks. Richness after a lift needed the right merge to
  accept arbitrary bijections.

**Graded milestone.** Any selector with YES lift value `>= c > 1/2`, uniformly in
`eta`, gives `Gap-Rich-2-to-1[c, 2 eta]` and `Gap-UG[c, eta]` on the same
instances. That is past the one-half wall of
`unique-games-hard-at-completeness-one-half` and
`rich-2to1-hard-at-completeness-one-half`.

**Relation to the other routes into this node.**

* `rich-2to1-from-perfect-completeness` asks for completeness 1 on rich
  instances and is dead for all known rich-producing constructions.
* The dead wrapper, gadget, conjugation and padding routes all try to *create*
  richness while preserving completeness. This route treats richness as solved
  and names completeness of one bit as the obstruction.
