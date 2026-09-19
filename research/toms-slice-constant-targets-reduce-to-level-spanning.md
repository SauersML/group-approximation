---
rg: 2
id: toms-slice-constant-targets-reduce-to-level-spanning
kind: claim
title: For overlap-window targets whose rank is constant on vertex slices, joint divisibility on each level component gives a budget delta + E <= N; one component spanning all but delta of the coordinates then forces depth ceil(N/2), which is sharp in this class
artifacts:
  - experiments/toms-overlap-window-nonsplit-2026-09-18/chern_component_sat.py
  - experiments/toms-overlap-window-nonsplit-2026-09-18/budget_scan.py
  - experiments/toms-overlap-window-nonsplit-2026-09-18/results.json
distinct_from:
  toms-overlap-window-drops-need-not-coincide: that applies the lcm argument once, globally, where rank Q = U everywhere, and proves ceil(N/2) only for targets that split over the nodes; this applies it on every level component of a target that need not split, and reduces ceil(N/2) to a spanning statement about level sets.
  toms-overlap-window-cubes-force-linear-depth: that is the full conjecture, for all targets; this settles it (with c = 1/2) for slice-constant targets, conditional on the spanning principle, and unconditionally for N <= 2.
---

**ESTABLISHED** (internal derivation, unreviewed; proof
`toms-slice-constant-targets-reduce-to-level-spanning-proof`). The spanning principle (S) below is
**OPEN** for `N >= 3`. It holds in a discretised model for `N <= 2`, but the `N = 3` check did
not finish.

**Setting.** As in `toms-overlap-window-drops-need-not-coincide`:
- `N` ideal two-wall windows `I_nu = A | w_1 | B | w_2 | C`, with `Pbar = k_nu + 1`,
  `Qbar = D - k_nu` and `kappa = 1`;
- the box `S = prod I_nu`, vertex slices `Y = prod CP^(j_nu)`, and the upper band `U = g' + N D`;
- `N D <= min j_nu`.

A target `Q` is *slice-constant* if, for some `z_0`, `rank Q(s, y, z_0)` depends only on `s`.
Write `delta(s) = U - rank Q(s, ., z_0)`. Then `delta >= 0` is an upper semicontinuous integer
function on `S`, and the depth is at least `max delta`.

A *level component* is a connected component `Omega` of a set `{delta = t}`. For an
interval `J ⊂ I_nu`, let `e(J)` be the number of chambers `J` meets, minus one. The exception
is a single wall point, where `e(J) = -1`. So `e = 0` inside one chamber (walls allowed as
endpoints), `e = 1` across one wall and `e = 2` across both. Put
`E(X) = sum_nu e(pi_nu X)`.

`Omega` *spans* `nu` if `pi_nu Omega` meets both `A` and `C`.

**Theorem.**
1. *Component budget.* Every level component `Omega` of a slice-constant target satisfies
   `delta(Omega) + E(cl Omega) <= N`. The closure refinement means `Omega` also pays for
   the walls its closure reaches.
2. *Reduction.* Suppose some level component `Omega` fails to span at most `delta(Omega)`
   coordinates. Then `delta(Omega) >= N/2`, so the depth is at least `ceil(N/2)`.
3. *Sharpness.* The staggered targets of Part 2 of `toms-overlap-window-drops-need-not-coincide`
   are slice-constant and have depth exactly `ceil(N/2)`. So `ceil(N/2)` is the best bound
   for this class.
4. *`N <= 2`.* The hypothesis of 2 holds for every upper semicontinuous `delta`. This is a
   Hex argument, and it recovers the `N = 2` bound for slice-constant targets.

**Spanning principle (S), open.** For every upper semicontinuous `delta : [0,1]^N -> Z_(>=0)`
and every choice of walls, some level component fails to span at most `delta(Omega)`
coordinates. By 1 and 2, (S) gives `c = 1/2` for every slice-constant target. That is
`toms-overlap-window-cubes-force-linear-depth` for this class, and the route yields
`eps_M >= 1/(4 d_n)` whenever the relevant targets are slice-constant.

**Model evidence** (`chern_component_sat.py`, results in `results.json`).
- *The model.* The box is a product cell complex, with each chamber cut into `m` open
  intervals and `m - 1` points. `delta` is constant on cells and upper semicontinuous along
  faces. Components are joined along faces of equal level. Only the basic budget
  `delta + E(Omega) <= beta` is imposed, not the closure refinement.
- *Minimal depth, general budget `beta`.* The minimal `max delta` is exactly
  `N - floor(beta/2)` for every `beta` in `0..2N`, at `N = 1, 2` (`m = 3`) and `N = 3`
  (`m = 2`).
- *At `beta = N`.* For `N = 3`, depth `1` is UNSAT at `m = 1, 2, 3, 4`, and depth `2` is SAT.
- *(S) itself.* It holds (no counterexample) for `(N, m) = (1,3), (2,3), (2,4)`. The
  `N = 3` instances timed out.
- *What this shows.* UNSAT is evidence at one resolution, not a proof. SAT is a model
  candidate only. The weight-3 form (T), "some point has `3 delta + sum a_nu >= 2N`", also
  holds in the model for `N <= 2`. The weight-2 form fails already at `N = 1`, at the bare
  node.

**Not settled.**
- (S) for `N >= 3`, or directly the bound `max delta >= N - floor(beta/2)` for the budget game.
  Candidate tools are Gale's `N`-dimensional Hex theorem and the Lebesgue partition theorem.
  A naive colouring argument fails: a component inside the middle strip `B` in coordinate
  `i` can link an `A`-side and a `C`-side component that both fail `i`.
- Targets whose rank varies along `Y`. On partial slices the Chern information is lost, and
  a drop along a hypersurface of `Y` costs only one unit. The budget of part 1 has no analogue
  there yet.
- Windows with `kappa >= 2`. The divisibility step of part 1 does not use the window shape, so
  it extends unchanged. Only the table of `e` changes, and part 2 would need the matching
  weighted form of (S).
