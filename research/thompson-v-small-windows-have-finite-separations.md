---
rg: 2
id: thompson-v-small-windows-have-finite-separations
kind: claim
title: Fifty small ball windows over Thompson's V carry no invariant-output strict pair, by finite images of their table groups
distinct_from:
  strict-pairs-transfer-to-table-realizations: that is the transfer theorem whose Corollary 3 turns a finite image of a window's table group into a rule-free exclusion; this is its computed instance on 50 explicit windows over V, with replayable witnesses.
  small-leavitt-invariant-output-windows-have-finite-separations: that is the computed exclusion of 44 windows over the binary Leavitt unit group, built with the Leavitt normal-form checker; this is over its subgroup V, with exact tree-pair arithmetic and different generating families.
  thompson-v-nonsurjunctive: that is the open existence problem for a strict automaton over V; this excludes the invariant-output pairs whose symmetry and memories lie in 50 explicit windows.
  large-window-table-groups-present-the-ambient-group: that shows above an explicit radius the table group of every window is V, so no finite image separates; this is the computed exclusion below that radius.
artifacts:
  - research/artifacts/thompson-v-window-screen-2026-09-12.md
  - experiments/gottschalk-thompson-v/v_window_screen.py
  - experiments/gottschalk-thompson-v/runs/results-excluded.json
---

**ESTABLISHED** by `thompson-v-window-separation-certificates`.

Let `V = G_(2,1)`, with elements stored as reduced tree-pair normal forms. For a finite
generating list `X`, radii `r_m, r_s`, and `h` of prime order `p`, put

    S = B_(r_s)(X),     M = <h> . B_(r_m)(X),

balls in `X u X^-1`. Let `U` be the table group: generators `x_a` for `a` in `S u M`,
with `x_1 = 1`, and relators

    x_s x_m = x_s' x_m'   whenever sm = s'm' in V,
    x_k x_m = x_(km)      for k in <h>, m in M.

The generators are named in Section 2 of the artifact: the Cannon–Floyd–Parry `A, B, C,
p0, p1`, the half turn `s`, and leaf permutations generating `S_4`, `A_5` and `GL(3,2)`.

**Theorem.** For each of the following 50 windows, some homomorphism from `U` into a
finite group sends `x_h` to a nontrivial element.

- **A character `U -> Z/p`** (24 windows):
  - t-cfp-order3 `1:1, 1:2, 2:1`;
  - t-cfp-half-turn `1:1`;
  - f-plus-p0, v-cfp-order2 and v-torsion-2-3, all four radii;
  - v-cfp-p1 and sym4-leaves-f, `1:1, 1:2, 2:1`;
  - alt5-leaves-f-order3 and gl32-leaves-f-order3, `1:1`.
- **A permutation image** (26 windows):
  - onto `A5`: v-cfp-order3 `1:1, 1:2, 2:1`; alt5-leaves-f-order2, all four radii;
    alt5-leaves-f-order3 `1:2, 2:1, 2:2`; t-cfp-order3 `2:2`;
  - onto `PSL(3,2)` in degree 7: gl32-leaves-v-order2, all four radii; t-cfp-half-turn
    `1:2, 2:1, 2:2`; gl32-leaves-f-order2 and gl32-leaves-f-order3, `1:2, 2:1`;
  - on cosets of index 3: v-torsion-2-3-order3, all four radii.

**Consequence.** Take any of these windows, any finite alphabet and any local rules. No
injective automaton over `V` has output invariant under `<h>` with memories `M' <= M`
and `S' <= S`, where `1` lies in both and `hM' = M'`. The certificate would realize its
window data in the finite image with `x_h != 1`. By Corollary 3 of
`strict-pairs-transfer-to-table-realizations`, such a pair is not strict there, a
contradiction.

**Not covered.**
- **Survive every test run.** Five windows at radius `2:2`: sym4-leaves-f, v-cfp-order3,
  v-cfp-p1, gl32-leaves-f-order2, gl32-leaves-f-order3. The tests were characters,
  targets through `PSL(2,11)`, and coset actions of index at most 6. Four of them also
  survive p-quotients of class at most 4, eleven larger simple targets, and index 7 to 9.
- **Unresolved.** gl32-leaves-f-order2 `1:1`, whose GAP search timed out.
- **Larger radii.** By `large-window-table-groups-present-the-ambient-group`, every
  window above radius `max(ceil(L/2), r_m, |h|)` has table group `V` and cannot be
  excluded this way.
- Other symmetries, and memories outside these balls.

The claim bears on `thompson-v-nonsurjunctive` only by excluding these windows.
