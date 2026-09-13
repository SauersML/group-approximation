---
rg: 2
id: rigid-unbalanced-two-patch-rules-beyond-class-ii-not-injective
kind: claim
title: Rigid unbalanced two-patch ternary rules outside class II are not injective over any group
distinct_from:
  rigid-two-patch-seed-rule-is-never-injective: that settles one rule of class I_3 by hand; this treats all 699 rigid unbalanced rules of classes I_3, I_1 and I_0, with swaps, cycles and three-site path moves.
  two-patch-ternary-rules-reduce-to-linear-strictness: that asks for every two-patch rule, rigid or not, to reduce to linear strictness; this is the rigid unbalanced census outside class II, with no unit hypothesis.
  unit-case-pair-distinct-two-patch-rules-are-not-injective: that treats class II, whose rules have no finite collision over free memory; every rule here has one.
  pair-distinct-ternary-rules-pre-injective-on-free-memory: that shows class II rules survive finite changes over free memory; the rules here collide over free memory, and what is open is the relations.
artifacts:
  - research/artifacts/rigid-two-patch-census-relation-moves-2026-09-12.md
---

**OPEN.** There is a candidate proof on paper for 486 of the 699 rules (see Attempts). w7-vf-nonlinear re-derived
its hand inputs (partial). The machine-generated minimal sets and counts are not re-derived. The `-proof` route
will be added once an independent re-derivation of those passes.

Let `G` be a group, `1, a, b` distinct elements of `G`, and `c = a^-1 b`. Put
`tau(x)(g) = mu(x(g), x(ga), x(gb))` over `F_3`, with `mu = lambda + t_p [y = p] + t_q [y = q]`.

**Claim.** Let `mu` be one of the 699 rules of classes `I_3`, `I_1` and `I_0` in the rigid census (artifact
`rigid-two-patch-seed-relation-moves-2026-09-12.md`, Section 6). Their linear parts are `x_1 + x_a - x_b` and
`x_1 + x_a`. Then `tau` is not injective over any `G`.

**Candidate coverage** (artifact `rigid-two-patch-census-relation-moves-2026-09-12.md`).
- **`I_3` and `I_1`** (504 rules).
  - Two-site moves over free memory fail only under a label `d^2 = 1` or `d^3 = 1`, with `d` in `a, b, c`.
  - A swap on `{1, d}` realizes on every nonamenable placement with `d^2 = 1`.
  - A cycle on `{1, d, d^-1}` realizes when `d^3 = 1`, provided its context pairs agree for each `e^2 = 1`.
  - Together these cover 468 rules, among them all 276 with linear part `x_1 + x_a`.
- **`I_0`** (195 rules).
  - Every rule has a three-site path move over free memory. Among its relators, nine Baumslag–Solitar words are
    dropped, and seven free-by-cyclic words and two torus-knot words are kept.
  - Swaps and cycles cover every nonamenable placement where one of `a^2`, `b^2`, `c^2`, `b^3`, `c^3` holds.
  - Together these cover 18 rules.
- **Amenable placements.** The Garden of Eden theorem and measure preservation force a balanced rule.

**Open.**
- **36 `I_1` rules**, such as `x_1 + x_a - x_b + [(0,1,0)] - [(0,2,1)]`. The proof is missing on nonamenable
  placements where `a^3 = 1` is the only label that holds, since no `a`-cycle exists.
- **177 `I_0` rules.** The proof is missing on nonamenable placements where none of `a^2`, `b^2`, `c^2`, `b^3`,
  `c^3` holds. For 159 of them, `<a, b | w>` with a kept word `w` is such a placement, and no move of the artifact
  realizes there.

**Scope.** Class `II` (30 rules) is `unit-case-pair-distinct-two-patch-rules-are-not-injective`. Non-rigid rules
are not treated.

## Attempts

- **Census relation moves** (w7-two-patch-census, artifact Sections 1–7).
  - **Inputs.** Hand relator tables (Sections 2, 3 and 6, with Lemma 6.1), and tiny `F_3` scripts in
    `research/artifacts/rigid-two-patch-census-scripts-2026-09-12/` for the move searches.
  - **Checks.** `explicit_moves.txt` replays every move used for one example rule of each census row.
  - **Verification** (w7-vf-nonlinear, 2026-09-12). Partial, Sections 1–3 and 6 re-derived, plus two Section 4
    replays (`w7-vf-nonlinear-verification-2026-09-12.md`, Section 4).
    - **Passed.** The hand inputs pass with notes: the level-1 relator table is complete for all three shapes by
      symmetry, Lemma 3.2 has no written proof, and the `c`-cycle table differs in form from the `a`-cycle table.
    - **Not re-derived.** The minimal sets, residuals, `I_0` closures and counts.
    - **Notes applied** (w7-two-patch-census). Section 2 of the artifact gives the symmetry argument for `1b` and
      `ab`. Section 3 proves Lemma 3.2 and writes out the `c`-cycle table. w7-vf-nonlinear verified these additions
      (PASS, Section 5 of the verification artifact).
- **Strict swaps** (superseded). Forcing equal values on the `e^2` context pairs of swaps left 174 rules open.
  Lemma 3.1 shows that no `e^2` holds beside `d^2` on a nonamenable placement, so those equalities are unnecessary.
- **Slow searches** (superseded). Two searches were too slow and were replaced by a feasibility search and a dynamic
  program:
  - enumerating all conflict sets of cycles (`level2.py`);
  - brute force over path contexts (`i0_path.py`).
- **First `I_0` table** (superseded, `i0_dp_before_bs_filter.txt`). It kept the nine `BS(1, ±2)` relators, which
  make the placement amenable.
- **Where it stops.** Artifact Sections 5–7. Next lead: three-site supports in `<a, b | a^3>` for the 36 rules,
  searched with the dynamic program of `i0_dp.py`.
