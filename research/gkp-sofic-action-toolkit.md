---
rg: 2
id: gkp-sofic-action-toolkit
kind: claim
title: GKP's permanence toolkit for sofic actions on countable sets
distinct_from:
  coordinate-action-not-sofic: that is one negative fact about one coset action of the Kun--Thom pair; this is the general positive machinery (restriction, orbits, locally finite stabilizers) that the negative fact is fed into
  single-lamps-recover-set-action: that is Alekseev--Bradford's halo-product criterion recovering a set action from a sofic C-action on the lamp group; this is the Gao--Kunnawalkam Elayavalli--Patchell set-action toolkit and mentions no lamps
  sofic-radical-hyperlinear-survivor: that is about which subgroups survive in the sofic radical of the wreath candidate; this is external permanence machinery for actions on sets
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
---

Four facts from Gao–Kunnawalkam Elayavalli–Patchell, *Soficity for group
actions on sets and applications*, arXiv:2401.04945v3 = *Res. Math. Sci.* **12**
(2025), 48. All four are about actions of a countable discrete group on a
countable discrete set, in that paper's Definition 2.1(5) sense — the same
sense used by `coordinate-action-not-sofic`.

> **Theorem 2.14.** Let `G` be a sofic group, `N ≤ G` be a locally finite
> subgroup of `G`. Then the left multiplication action `α : G ↷ G/N` is
> sofic.

> **Proposition 2.15.** (2) If `α : G ↷ X` is sofic, then the restriction of
> `α` to each of its orbits is sofic; (3) If `α : G ↷ X` is sofic and `H` is
> a subgroup of `G`, then `α|_H` is sofic; (4) If `G_1 ⊆ G_2 ⊆ ⋯` is an
> increasing sequence of subgroups of `G` whose union is `G`, and
> `α : G ↷ X` restricted to each `G_i` is sofic, then `α` is sofic.

> **Proposition 2.16.** If the restriction of `α : G ↷ X` to each of its
> orbits is sofic, then `α` is sofic.

Two consequences used repeatedly downstream, both immediate:

- **The regular action of a sofic group is sofic.** Theorem 2.14 with
  `N = {1}`, the trivial group being locally finite. Hence every *free*
  action of a sofic group on a countable set is sofic, by Proposition 2.16:
  each orbit of a free action is `G`-isomorphic to `G/{1}`, and soficity of
  an action depends only on the isomorphism class of the `G`-set (visible in
  the paper's own ultraproduct form, Proposition 2.9(2): a `G`-equivariant
  bijection transports `π` and leaves `φ` alone).
- **Soficity of an action is orbitwise.** Proposition 2.15(2) and Proposition
  2.16 together: `α` is sofic **iff** each of its orbits is. So a nonsofic
  action of any group always contains a nonsofic *transitive* orbit, i.e. a
  nonsofic `G ↷ G/H` for `H` a point stabilizer. This is what lets
  `nonsofic-orbit-forces-commuting-counterexample` assume transitivity for
  free.

**Trust surface.** Refereed journal article; verbatim transcription from the
v3 PDF recorded in the artifact. Not formalized anywhere in this repository.
The graph already leans on the same paper's Theorem 3.6 (generalized wreath
products) inside `coordinate-action-not-sofic-proof`, so this node does not
enlarge the trust surface — it names the part of it that the
commuting-actions lane consumes.

## What the paper does *not* give

At publication the authors write, in the same section: *"It is still open
whether all actions by sofic groups are sofic."* Theorem 2.14 is their only
general positive result about non-amenable acting groups, and they record
explicitly that they cannot settle even the case of amenable stabilizers. The
missing negative example arrived a year later from Kun–Thom and is
`coordinate-action-not-sofic`.
