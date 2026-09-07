---
rg: 2
id: kervaire-laudenbach-mf-overgroup-proof
kind: route
title: Retain a faithful norm-corona embedding while adjoining roots
target: kervaire-laudenbach-holds-for-mf
requires:
  - nonsingular-adjunction-preserves-approximation-radicals
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

Start with a faithful norm-corona embedding of the coefficient group.
The prerequisite extends it to the relative presentation. Its restriction
remains the faithful map, so the coefficient map is injective; its countable
image is the required MF solution group. Section 5 proves this and explains
why the extension is not assumed faithful on new-variable words.

Inside the same corona, adjoin roots for every nonsingular equation over
the current countable subgroup, then repeat over the larger countable
subgroup. Their union is still countable and MF. Every finite coefficient
list occurs at one stage and receives a root at the next, proving the
equation-solving closure assertion.
