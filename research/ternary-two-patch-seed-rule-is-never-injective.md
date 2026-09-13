---
rg: 2
id: ternary-two-patch-seed-rule-is-never-injective
kind: claim
title: The two-patch ternary seed x_1 - x_a + x_b + [(0,1,2)] + [(1,2,0)] is not injective over any group, and not pre-injective when its memory group is nonamenable
distinct_from:
  two-patch-ternary-rules-reduce-to-linear-strictness: that asks whether every two-patch rule sharing a symbol is injective only where its linear part is a linear strict automaton; this settles its smallest named seed outright, with no linear strict automaton and no unit hypothesis.
  pair-distinct-ternary-rules-pre-injective-on-free-memory: that shows some rigid ternary rules survive every finite perturbation over free memory; this seed is not rigid, and finite perturbations kill it on every nonamenable placement.
artifacts:
  - research/artifacts/two-patch-seed-relation-moves-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `ternary-two-patch-seed-never-injective-proof`. Verified by w3-vf-nonlinear, who
re-derived every coincidence table (`w3-vf-nonlinear-verification-2026-09-12.md`, Section 28, commit
73bc73756f).

Let `G` be a group and `1, a, b` distinct elements of `G`. Let
`mu_2(y_1, y_a, y_b) = y_1 - y_a + y_b + [y = (0,1,2)] + [y = (1,2,0)]` over `F_3`, and
`tau(x)(g) = mu_2(x(g), x(ga), x(gb))`.

**Theorem.** `tau` is not injective. If `<a, b>` is nonamenable, `tau` is not even pre-injective. The
collision changes one or two sites:
- **No involution among `a`, `b`:** change one site by `+1` (artifact Lemma 1).
- **`a^2 = 1`:** change `h` and `ha` by `+1` (Lemma 2).
- **`b^2 = 1`:** change `h` by `+1` and `hb` by `-1` (Lemma 3).

Every relation that breaks these tables makes `<a, b>` amenable. There the Garden of Eden theorem and
measure preservation force a balanced rule, but `mu_2` has value counts `10, 8, 9`.

**What it corrects.** The seed was listed as open because both unit-case methods of
`distinct-symbol-patch-collision-2026-09-12.md` leave a residue there. But `{0, 1}` is a blind pair of
all three coordinates, so the seed is not rigid, and single-site changes do work. Census Proposition 5.1
(`small-memory-balance-census-2026-09-12.md`) covers the Sidon placements. The artifact settles the
relation cases for this rule.

**Scope.** This settles one rule. Rigid two-patch rules, with no common blind pair, are still open; the
artifact's Section 4 gives the blind-pair criterion and the next seed.
