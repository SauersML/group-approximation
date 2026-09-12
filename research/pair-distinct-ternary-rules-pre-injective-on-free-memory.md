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

**Example.** The census rule `R = x_1 - x_a + x_b + [(x_1, x_a, x_b) = (0, 2, 2)]` over `Z/3`
qualifies (w4-bal-census).
- Its diagonal is the identity, so it passes the constant tests.
- It is unbalanced, with value counts `(8, 10, 9)`.
- Each address has exactly one insensitive context: `(x_a, x_b) = (2,2)` identifies `{0,1}`,
  `(x_1, x_b) = (0,2)` identifies `{1,2}`, and `(x_1, x_a) = (0,2)` identifies `{0,2}`.

The first example given here, `x_1 + x_a + x_b + [x = (0,1,2)]`, also meets the hypothesis. But it
sends every constant configuration to `0`, so it is never injective. It illustrates pre-injectivity
only.

**Consequence.** Constant backgrounds, rectangle relations, glued flips and finite-subgroup screens
all compare finitely different configurations, and none of them excludes such rules. The rule is not
injective over `F(a, b)`, because free groups are sofic and injectivity would force balance, so the
failure there is global. A counterexample built from these rules needs relations that stop infinite
defect cascades. This is the open target `affine-plus-defect-rule-is-injective-on-some-group`.

**Where such rules die over other groups.**
- **Linear part not a unit.** By `avoidable-patches-of-affine-rules-inherit-linear-injectivity`, `R`
  is injective over `G` only if `1 - a + b` is a unit of `F_3[G]`, or `G` already carries a linear
  strict automaton.
- **Linear part a unit.** On three ternary addresses, distinct pairs with a unit linear part force
  `p` to omit a symbol. `R` omits `1`. Then a constant background at the omitted symbol, plus the
  inverse correction creating one defect, gives two configurations with the same image. This fails
  only if a memory translate is absorbed (`constant-background-kills-unit-linear-defect-rules`).
- **What the pre-injectivity result shows.** It locates where finite perturbations stop. It does not
  supply a candidate host.

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
