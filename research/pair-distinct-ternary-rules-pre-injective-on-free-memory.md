---
rg: 2
id: pair-distinct-ternary-rules-pre-injective-on-free-memory
kind: claim
title: Ternary rules on three free memory letters whose insensitive contexts identify distinct pairs are pre-injective, so finite-perturbation screens are silent on them
distinct_from:
  three-address-binary-injective-rules-are-balanced: that kills every unbalanced binary rule on three memory elements through finite flips; this shows that over the ternary alphabet some unbalanced rules on three addresses have no finite invisible perturbation at all over the free realization.
  free-memory-injectivity-forces-universal-bijectivity: that says an encoder injective over free memory is bijective everywhere; this is about pre-injectivity over free memory, which unbalanced rules can have while failing injectivity globally.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `pair-distinct-ternary-rules-pre-injective-on-free-memory-proof`.

**Statement.**
- **Setting.** `A = Z/3` and `M = {1, a, b}`, realized as free generators of `F(a, b)`.
- **Hypothesis.** At each address `m`, every insensitive context of the rule identifies exactly one
  fixed pair `P_m` and is injective otherwise, and `P_1`, `P_a`, `P_b` are distinct.
- **Conclusion.** The automaton over `F(a, b)` is pre-injective.

**Example.** The rule `mu = x_1 + x_a + x_b + [(x_1, x_a, x_b) = (0, 1, 2)]` over `Z/3` qualifies.
- It is unbalanced, with value counts `(8, 10, 9)`.
- Each address has exactly one insensitive context, identifying `{0,1}`, `{1,2}` and `{0,2}`
  respectively.

**Consequence.** Constant backgrounds, rectangle relations, glued flips and finite-subgroup screens
all compare finitely different configurations, and none of them excludes such rules. The rule is not
injective over `F(a, b)`, because free groups are sofic and injectivity would force balance, so the
failure there is global. A counterexample built from these rules needs relations that stop infinite
defect cascades. This is the open target `affine-plus-defect-rule-is-injective-on-some-group`.

**Relation to the census.** Pair-distinct rules are rigid in the sense of `w4-bal-census`: no pair is blind
in every coordinate. So they are exactly where `ternary-three-address-injective-automata-have-balanced-rules`
is open. This result says a proof of that claim cannot use finitely supported perturbations over free
memory. For binary rules the analogous single flip always exists on Sidon memory
(`binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective`).

**Why.** A block reading exactly one changed site hides the change only if its address pair equals the
change pair. So every changed site lies in two triangles `{h, ha, hb}` holding another changed site.
Over the free group, the incidence graph between sites and triangles is a forest. Counting its edges
gives a contradiction.

Artifact, Section 3, Proposition 10.
