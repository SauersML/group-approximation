---
rg: 2
id: leavitt-unit-group-surjunctive
kind: claim
title: The binary Leavitt unit group is surjunctive
root: true
refuted_by:
  - leavitt-unit-group-nonsurjunctive
distinct_from:
  leavitt-unit-group-nonsurjunctive: that is the negation, seeking an injective nonsurjective automaton; this is the positive assertion for the same group.
  gottschalk-surjunctivity-conjecture: that asserts surjunctivity of every group; this is the case of the first nonsofic group, which that conjecture implies and which does not imply it.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
  - research/artifacts/gottschalk-sofic-radical-localization-2026-09-11.md
---

**OPEN.** For `U = L_(F_2)(1,2)^x` and every finite alphabet `A`, every injective cellular automaton `A^U -> A^U` is surjective.

*Marked `root` because it is the positive side of an external question: does the first nonsofic group satisfy Gottschalk's conjecture? It is refuted exactly when `leavitt-unit-group-nonsurjunctive` is established.* Thompson's group `V <= U` would inherit it.

## Attempts

* **Permanence theorems.**
  * `rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive`, `finitary-split-extension-surjunctivity-permanence`, `doubles-of-surjunctive-groups-are-surjunctive` and `lef-lamp-graph-wreaths-are-surjunctive` all prove surjunctivity of an extension with a residually finite or LEF kernel over a surjunctive quotient.
  * Direct limits of surjunctive groups are surjunctive.
  * These tools cannot reach `U` without assuming the conclusion for a group containing `U`. A finitely generated simple nonsofic subgroup of such a group meets the kernel trivially and embeds in the quotient, or lies in one stage of the limit.
* **Marked limits.** Nonsurjunctivity is an open condition in the space of marked groups. But `U` is finitely presented and simple, hence finitely discriminable and isolated (Cornulier–Guyot–Pitsch). So nothing approximates it.
* **Counting.** Gromov–Weiss counting along permutation models is vacuous here, because `U` has full sofic radical (Theorem D of the radical-localization artifact).
* **Entropy, 2026-09-12.** `positive-rokhlin-entropy-makes-leavitt-units-surjunctive` reduces this claim to one free ergodic action of `U` with positive Rokhlin entropy. That is the open claim `leavitt-unit-group-has-positive-rokhlin-entropy-action`. No lower bound for Rokhlin entropy is known without sofic models.
