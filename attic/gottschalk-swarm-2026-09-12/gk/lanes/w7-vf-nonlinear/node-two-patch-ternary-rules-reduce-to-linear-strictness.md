---
rg: 2
id: two-patch-ternary-rules-reduce-to-linear-strictness
kind: claim
title: A ternary three-address rule that differs from an affine rule at two patterns sharing a symbol is injective only where its linear part is a linear strict automaton
distinct_from:
  distinct-symbol-patch-ternary-rules-reduce-to-linear-strictness: that settles one patch with distinct symbols; this is two patches, where the one-coordinate breaker fails on the support of the delta preimage whenever every coordinate carries two patch symbols.
  single-patch-ternary-rules-reduce-to-linear-strictness: that settles one patch with a repeated symbol.
artifacts:
  - research/artifacts/distinct-symbol-patch-collision-2026-09-12.md
---

**OPEN.** Let `A = F_3`, `G` a group, `M = {m_1, m_2, m_3}` three distinct elements, and `lambda` affine with
linear automaton `L`. Let `mu = lambda + t_p [pattern = p] + t_q [pattern = q]` with `p != q`, nonzero weights,
and some symbol occurring in both `p` and `q`. If `tau_mu` is injective over `G`, then `L` is an injective,
non-surjective linear automaton over `G`.

A two-patch rule is at distance 2 from its affine rule. Together with the single-patch reductions, this is
the next case of `ternary-three-address-injective-automata-have-balanced-rules` beyond linear strict
automata. A counterexample refutes Gottschalk's conjecture.

## Attempts

- **Non-unit case: done.** The shared symbol makes `avoidable-patches-of-affine-rules-inherit-linear-injectivity`
  apply, so `L` is injective. A non-unit linear part is then not surjective.
- **Coordinate breakers** (artifact Proposition 4). Theorem 1's scheme runs at coordinate `i` only if
  `p_i = q_i`. If `p` and `q` differ at every coordinate, no single-coordinate breaker survives at any site
  where the delta preimage is nonzero.
- **Constant background** (artifact Proposition 5). In the unit case a collision holds except on the windows
  carrying `M \ P_c` into `M ∪ N^-1`, for each admissible background `c` and each choice of patch. The
  residue is finite but grows when the patches use `c` at more addresses.
- **Seed.** `(x_1 - x_a + x_b) + [(0,1,2)] + [(1,2,0)]` uses two patch symbols at every address. Both unit-case
  methods leave a residue there. Unused freedoms:
  - break the two configurations at different sites;
  - cancel equal-weight occurrences `(0,1,2)` and `(1,2,0)` where the preimage reads `(1,1,1)`;
  - vary the background near the support.
- **Where it stops.** No collision is known for the seed over a group where `1 - a + b` is a unit and its
  inverse support absorbs single-address translates. No obstruction to such a collision is known either.
- **Seed closed** (w5-two-patch, `ternary-two-patch-seed-rule-is-never-injective`, artifact
  `two-patch-seed-relation-moves-2026-09-12.md`; verified by w3-vf-nonlinear, 73bc73756f).
  - **Not rigid.** `{0, 1}` is a blind pair of all three coordinates.
  - **Nonamenable placements.** One-site collisions work unless `a^2 = 1`, `b^2 = 1`, `ab = 1`, `b = a^2`
    or `a = b^2`, and two-site moves cover `a^2 = 1` and `b^2 = 1`.
  - **Amenable placements.** The Garden of Eden theorem and measure preservation force a balanced rule.
  - **Net.** The seed is not injective over any group, unit case included. The entry "Where it stops"
    above is superseded for the seed.
- **Blind-pair criterion** (same artifact, Proposition 4).
  - **Statement.** For patches at distance two or more, coordinate `i` with `c_i != 0` is blind exactly
    for the pairs `F_3 \ {r_i - t_r c_i^-1}`, `r` in `Pi`.
  - **Non-rigid rules.** They are excluded on Sidon placements by census Proposition 5.1. Their relation
    cases are open beyond the seed.
  - **Classes.** Augmentation-0 coefficient classes never reach the unit case, and rules with one nonzero
    coefficient are never rigid.
- **Next seed.** `(x_1 + x_a - x_b) + [(0,0,2)] + [(1,2,0)]`.
  - **Data.** Rigid, with two patch symbols at every address, augmentation 1 and counts `8, 9, 10`.
  - **Where the methods stop.** Proposition 5 has no background `0`. Backgrounds `1` and `2` leave
    residues at `{a, b}` and `{1}`.
- **Next seed closed** (w7-two-patch-rigid, `rigid-two-patch-seed-rule-is-never-injective`, artifact
  `rigid-two-patch-seed-relation-moves-2026-09-12.md`; verified by w7-vf-nonlinear, Section 1 of
  `w7-vf-nonlinear-verification-2026-09-12.md`).
  - **Free memory.** Every pair is blind at two coordinates, so three two-site moves exist.
  - **Relations.** Their conflicts force an amenable group except under `(a^-1 b)^2 = 1`, where a fourth
    two-site move realizes. If all three fail otherwise, `<a, b>` is a quotient of a finite or Euclidean
    triangle group.
  - **Net.** The next seed is not injective over any group, unit case included. "Where the methods stop"
    above is superseded for it.
- **Uniform filters** (same artifact, Section 5).
  - **Constants.** If `v -> mu(v, v, v)` is not injective, `tau_mu` is not injective over any group.
  - **Marked quotients.** Injectivity descends to marked quotients. So an injective unbalanced rule restricts
    to a balanced rule on the coincidence pattern of `1, a, b` in every amenable quotient.
- **Free-memory census** (same artifact, Section 6). There are 855 raw rigid unbalanced two-patch rules.
  - **Constants.** 126 of them collapse on constants.
  - **Classes `I_3` and `I_1`** (504 rules). They have two-site collisions over free memory. Relation tables
    are done only for the next seed.
  - **Class `I_0`** (195 rules). Collisions need three or more sites. Not searched.
  - **Class `II`** (30 rules, pair-distinct). No finite collision over free memory, by
    `pair-distinct-ternary-rules-pre-injective-on-free-memory`.
- **Smallest open case.** `unit-case-pair-distinct-two-patch-rules-are-not-injective`, with seed
  `x_1 + x_a - x_b + [(0,1,0)] - [(1,2,2)]`.
