---
rg: 2
id: fpbs-percolation-schreier-kesten-gap
kind: claim
title: Slightly supercritical clusters meet any infinite non-co-amenable subgroup only finitely often, giving a relative threshold gap
distinct_from:
  fpbs-relative-gap-along-any-subgroup-separates: that proves a relative gap along any infinite subgroup implies p_c < p_u, but produces no gap; this asserts the gap for every infinite subgroup whose Schreier graph is nonamenable.
  fpbs-tree-subgroup-relative-gap-iff-not-co-amenable: that proves this statement on the free-group tree, where two-point functions are explicit; this asserts it on every Cayley graph of every finitely generated group.
  fpbs-tree-normal-relative-threshold-is-inverse-cogrowth: that is the normal-subgroup tree case with exact thresholds; this is a gap statement on all Cayley graphs and for non-normal subgroups.
  fpbs-amenable-wq-normal-relative-subcriticality: that is finite relative susceptibility along one amenable wq-normal subgroup, equivalent to the threshold gap for that group; this is the special case of that statement for amenable wq-normal subgroups, extended to every non-co-amenable subgroup, which includes all amenable subgroups of nonamenable groups and every normal subgroup with nonamenable quotient.
  fpbs-central-amenable-relative-threshold-is-pu: that computes p_c(I;G) = p_u(G) for amenable I in groups with infinite centre; this conjectures p_c(G) < p_c(I;G) for them, which there is exactly p_c < p_u.
artifacts:
  - experiments/fpbs-schreier-kesten-2026-09-17/verify_schreier_cogrowth_identity.py
  - experiments/fpbs-schreier-kesten-2026-09-17/output.txt
---

**OPEN.**

**Setting.** Let `Gamma` be finitely generated, `S` a finite symmetric
generating set, and `G = Cay(Gamma,S)`. Let `I <= Gamma` be an infinite
subgroup that is **not co-amenable**: there is no `Gamma`-invariant mean on
`ℓ^∞(I\Gamma)`. By the standard Følner–Eymard equivalence, this means the
Schreier graph `Sch(I\Gamma,S)` is nonamenable. Part (a) of
`fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap` proves the
direction used here, spectral radius `< 1`.

**Statement.**

```text
p_c(G) < p_c(I;G),
```

or equivalently `chi^I_p = E_p|K_o ∩ I| < infinity` for some `p > p_c(G)`
(`fpbs-relative-gap-along-any-subgroup-separates`, which then also gives
`p_c(G) < p_u(G)`).

This is a percolation analogue of Kesten's criterion, stated for coset spaces.
The random walk sees the Schreier graph through `P(SRW_n in I)`; the
conjecture asks that slightly supercritical Bernoulli clusters see it the same
way.

**Special cases.**
- **Trees.** It holds on `T = Cay(F_d, free basis)` for every infinite
  subgroup, and it is sharp there: spectral radius one kills the gap
  (`fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`).
- **Normal subgroups.** For normal `I = N` the Schreier graph is
  `Cay(Gamma/N)`, so the statement contains the percolation Kesten normal gap:
  an infinite normal `N` with nonamenable quotient gives
  `p_c(G) < p_c(N;G)`. That is the claim `fpbs-percolation-kesten-normal-gap`
  on origin/main, not yet in this worktree.
- **Amenable subgroups of nonamenable groups.** They are never co-amenable
  (part (b) of
  `fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`). So the
  statement contains `fpbs-amenable-wq-normal-relative-subcriticality` for
  every Cayley graph. On that class it is equivalent to `p_c < p_u`
  (`fpbs-amenable-wq-normal-pu-is-relative-pc`). **So this premise is at least
  as strong as the goal on the amenable-wq-normal class.** What it buys is a
  single uniform statement covering every nonamenable group outside the
  residual class of `fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness`.
- **Cyclic subgroups.** The statement restricted to `I = <g>`, `g` of infinite
  order, already implies `p_c < p_u` for every nonamenable group that is not
  periodic.

**Where it sits.**
- *The route.* `fpbs-bs-via-percolation-schreier-kesten-split` combines it with
  the residual class `fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness`
  to give `fpbs-benjamini-schramm-universal`. That residual class is periodic,
  has no infinite amenable subgroup, and contains the Tarski monsters.
- *The two premises fail independently.* A failure here along a non-normal
  subgroup `I` of some product need not refute Benjamini–Schramm. A Tarski
  monster with `p_c = p_u` would refute the residual premise and say nothing
  here, since a Tarski monster has no infinite non-co-amenable subgroup.

## Attempts

- **2026-09-17, b-d-bs-transplant, group-rings: tree calibration.**
  **Established.** Proved on `F_d` for all subgroups
  (`fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`). Grigorchuk's word
  recursion `A_n A = A_(n+1) + q A_(n-1)` acts on cosets without normality.
  Pringsheim at both radii then gives:
  - `R_H > 1/q` iff `rho(Sch) < 1`;
  - `chi^H_p = infinity` for every `p > 1/q` when `rho(Sch) = 1`.

  The coefficient identity was checked on `<a>`, `<a, b a b^-1>` and a
  finite-index point stabiliser (script in `artifacts`). What transfers: the
  tree is the calibration any proof must pass, and the criterion is spectral
  radius, not normality.
- **2026-09-17, b-d-bs-transplant: naive random-walk majorant.**
  **Dies as a general route.** BK, and counting self-avoiding paths by all
  walks, give

  ```text
  chi^I_p <= sum_(h in I) tau_p(o,h) <= sum_n (pD)^n P(SRW_n in I) <= sum_n (p D ||P_Sch||)^n .
  ```

  This proves the gap whenever `||P_Sch|| < 1/(D p_c(G))`, where `D = |S|`. The
  bound dies already on the tree: for `T_4` (`D = 4`, `p_c = 1/3`) it needs
  `||P_Sch|| < 3/4`. For `I = <a>`, the Schreier graph is a tree with loops,
  whose spectral radius is at least `rho(T_4) = sqrt 3/2 > 3/4`, since it
  contains arbitrarily large balls of `T_4`. Yet the true relative threshold is
  `1`, because `R_H = 1`. The loss is replacing `tau_p` by the walk count, which is off by the
  factor `mu/D` in the exponential rate even at `I = Gamma`. Any working proof
  must use tree-likeness of slightly supercritical clusters, not walk counting.
- **2026-09-17, b-d-bs-transplant: counterexample search.** **None found.**
  - *Normal subgroups.* A counterexample must be an infinite subgroup with
    nonamenable Schreier graph that slightly supercritical clusters meet
    infinitely often in expectation. For normal `I` this would contradict the
    heuristic that fibre visits are governed by `sum m^n P(SRW_n in I)` near
    `m = 1`, and the tree case.
  - *Products and centres.* On products `Cay(H) □ T` and on groups with
    infinite centre, the amenable case reduces to `p_c < p_u`, which is
    unknown there but not contradicted.
  - *Status.* The claim stays OPEN.
