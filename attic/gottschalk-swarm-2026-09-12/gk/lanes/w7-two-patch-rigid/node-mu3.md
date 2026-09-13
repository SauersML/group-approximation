---
rg: 2
id: rigid-two-patch-seed-rule-is-never-injective
kind: claim
title: The rigid two-patch ternary seed x_1 + x_a - x_b + [(0,0,2)] + [(1,2,0)] is not injective over any group, and not pre-injective when its memory group is nonamenable
distinct_from:
  ternary-two-patch-seed-rule-is-never-injective: that settles the non-rigid seed, where one pair is blind at all three coordinates and single-site changes work; here no pair is blind at three coordinates, so every collision needs two sites.
  two-patch-ternary-rules-reduce-to-linear-strictness: that asks for the whole two-patch class; this settles its named rigid seed outright, with no unit hypothesis.
  pair-distinct-ternary-rules-pre-injective-on-free-memory: that shows rules with three distinct blind pairs survive finite changes over free memory; here every pair is blind at two coordinates, and two-site changes kill the rule on every nonamenable placement.
artifacts:
  - research/artifacts/rigid-two-patch-seed-relation-moves-2026-09-12.md
---

**OPEN.** There is a candidate proof on paper (see Attempts). Verification was requested from w3-vf-nonlinear,
with no verdict yet. The `-proof` route will be added once the verifier's independent re-derivation passes.

Let `G` be a group and `1, a, b` distinct elements of `G`. Let
`mu_3(y_1, y_a, y_b) = y_1 + y_a - y_b + [y = (0,0,2)] + [y = (1,2,0)]` over `F_3`, and
`tau(x)(g) = mu_3(x(g), x(ga), x(gb))`.

**Claim.** `tau` is not injective. If `<a, b>` is nonamenable, two configurations that differ at two sites have
the same image.

**Candidate collisions.** Put `c = a^-1 b`.
- **Free memory.** Three two-site moves `T_ab`, `T_1a` and `T_1b`, one for each pair blind at two coordinates
  (artifact Section 1).
- **Relations** (Section 2). On a nonamenable placement:
  - `T_ab` fails only if `c^2 = 1` or `c^3 = 1`;
  - `T_1a` fails only if `a^2 = 1`, `a^3 = 1` or `c^2 = 1`;
  - `T_1b` fails only if `b^2 = 1`, `b^3 = 1` or `c^2 = 1`.

  So if all three fail and `c^2 != 1`, `<a, b>` is a quotient of a finite or Euclidean triangle group.
- **`c^2 = 1`.** A fourth two-site move realizes in every such group (Section 3).
- **Amenable placements.** The Garden of Eden theorem and measure preservation force a balanced rule. The value
  counts of `mu_3` are `8, 9, 10`.

**What it corrects.** In the parent claim, "Where the methods stop" under the next seed records residues of both
unit-case methods. Two-site changes need no unit hypothesis and no background.

**Scope.** This settles one rule.
- **Census.** Artifact Section 6 classifies every rigid unbalanced two-patch rule by its free-memory moves.
- **Smallest open case.** Rules with three distinct blind pairs, which have no finite collision over free
  memory: `unit-case-pair-distinct-two-patch-rules-are-not-injective`.

## Attempts

- **Candidate proof** (w7-two-patch-rigid, artifact `rigid-two-patch-seed-relation-moves-2026-09-12.md`,
  Sections 1–4).
  - **Inputs.** For amenable placements, `bijective-ca-preserve-uniform-bernoulli-measure` and the Garden of Eden
    theorem. Otherwise, hand window tables and a hand classification of relators.
  - **Checks.** The tables were replayed with tiny `F_3` scripts.
  - **Verification.** Requested from w3-vf-nonlinear.
