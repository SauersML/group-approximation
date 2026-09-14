---
rg: 2
id: binary-four-address-injective-automata-have-balanced-rules
kind: claim
title: Over every group, an injective two-symbol automaton with four memory elements has a balanced rule
distinct_from:
  three-address-binary-injective-rules-are-balanced: that settles three memory elements, where every relation blocking a flip makes the memory group amenable; this is four elements, where placements such as {1, a, b, ab} force coincidences among memory quotients in every group.
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
---

**OPEN.** Let `G` be any group, `M` a subset of `G` with `|M| = 4`, and
`mu : {0,1}^M -> {0,1}`. If `tau(x)(g) = mu((x(g m))_(m in M))` is injective, then `mu` is
balanced.

This is a case of `every-injective-ca-has-uniform-single-site-output-law`. A counterexample
refutes Gottschalk's conjecture.

## Attempts

- **Sidon placements.** Excluded by `binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective`.
- **Constant tests.**
  - The diagonal must be a permutation, and a flip of a constant must be visible.
  - Parity patched at one cell dies by these tests.
- **Placements that are Sidon in no group.** Dies here.
  - **Example.** `{1, a, b, ab}` has `a^-1 (ab) = b` and `(ab)^-1 a = b^-1` in every group.
  - **Constraints.** The single flip needs blind patterns with `r_1(b) = r_a(ab)` and
    `r_ab(a) = r_b(1)`.
  - **Not done.** Rules whose blind patterns violate these constraints need double flips or larger
    perturbations, and no census of them was done.
- **Design form.** A refuting design needs a table-group relator `m^-1 m' = n^-1 n'` among its
  memory letters (artifact, Corollary 3.3), whether or not the letters themselves collide.
- **Census of single flips and table groups (gk3-bernoulli-preservation, 2026-09-14).**
  `binary-four-address-single-flip-balance-census` (computer assisted) excludes 664 of the 859
  unbalanced rule classes over every group. It solves single invisible flips on all 1124 quotient
  partitions, then decides each minimal failing table group exactly, using amenable memory groups
  and Garden of Eden.
  - **Exact gap.** 195 rule classes remain. Each needs a group with no invisible single flip whose
    memory group is a quotient of one of 160 table groups:
    - 131 non-amenable free products of cyclic groups, the simplest `Z/2 * F_2` and `F_2`;
    - 13 non-amenable graph products;
    - 16 undecided.
  - **Next step.** Double flips and larger perturbations on those survivors (artifact Section 4),
    which a counterexample must also defeat.
  - Artifact: `research/artifacts/gk3-four-address-balance-census-2026-09-14.md`.
