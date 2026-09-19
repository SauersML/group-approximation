---
rg: 2
id: toms-two-level-spanning-holds-in-every-dimension
kind: claim
title: The spanning principle holds in every dimension when delta takes only the values 0 and 1, so slice-constant targets have depth at least 2 once beta <= 2N - 3, and the ceil(N/2) bound holds for N = 3 and N = 4
artifacts:
  - experiments/toms-level-spanning-weighted-2026-09-18/anneal.c
  - experiments/toms-level-spanning-weighted-2026-09-18/results.json
distinct_from:
  toms-slice-constant-targets-reduce-to-level-spanning: that proves the budget delta + E <= N and reduces ceil(N/2) to the spanning principle (S), proving (S) only for N <= 2 by planar Hex; this proves (S) in every dimension for two-valued delta, by a fill argument that planar Hex does not give, and deduces the depth bound for N = 3, 4.
---

**ESTABLISHED** (internal derivation, unreviewed; proof
`toms-two-level-spanning-holds-in-every-dimension-proof`).

**Setting.** As in `toms-slice-constant-targets-reduce-to-level-spanning`:
- `delta : [0,1]^N -> Z_(>=0)` is upper semicontinuous;
- each coordinate carries two walls, `A | w_1 | B | w_2 | C`;
- a *level component* is a connected component of some `{delta = t}`.

Say that a set *face-spans* the coordinate `nu` if it meets both faces `{x_nu = 0}` and
`{x_nu = 1}`. Face-spanning implies spanning in the sense of that claim (meeting `A` and `C`).

**Theorem.**
1. *Two-level spanning principle.* Let `H ⊂ [0,1]^N` be closed, `N >= 2`, and suppose no
   component of `H` face-spans `N - 1` or more coordinates. Then some component of the
   complement face-spans all `N` coordinates. Equivalently, (S) holds whenever
   `max delta <= 1`: some level component `Omega` fails to span at most `delta(Omega)`
   coordinates.
2. *Depth 2.* In the budget game `delta(Omega) + E(cl Omega) <= beta` for every level
   component, `beta <= 2N - 3` forces `max delta >= 2`. For slice-constant targets
   (`beta = N`), the depth is at least `2` for every `N >= 3`.
3. *`N = 3, 4`.* For `N = 3` and `N = 4`, slice-constant targets have depth at least
   `ceil(N/2) = 2`, and this is sharp (staggered targets). More generally, the bound
   `max delta >= N - floor(beta/2)` holds whenever `N - floor(beta/2) <= 2`, that is
   `beta >= 2N - 4`.

**What is new.** Planar Hex (the `N = 2` case) does not extend by colouring. The known
obstruction is chaining through middle-strip components. The proof here avoids colourings.
- Each component `K` of `H` misses a face in two different coordinates, and the missed faces
  form a connected set `G_K`.
- The *fill* of `K` is everything except the complementary component that contains `G_K`.
  Fills are laminar.
- The maximal fills do not separate the cube (Phragmén-Brouwer property of the unicoherent
  cube), and none of them contains a face.
- So the part of the complement outside all fills is connected and meets all `2N` faces.

**Obstructions to the general case** (also proved in the proof file). They mark the exact
step where the two natural inductions on levels die.
- *Top-down peeling.* Theorem 1 gives a component `Y` of `{delta >= 1}` that spans `N - 1`
  coordinates. Recursing inside `Y` would need Theorem 1 relative to the continuum `Y`. That
  relative statement is false once `Y` is not unicoherent: a loop around a square face, cut
  at two opposite corners, is a counterexample. So any proof of (S) for `max delta >= 2`
  must use the lower levels, not only the continuum `Y`.
- *Bottom-up peeling.* Replacing `delta` by `max(delta - 1, 0)` reduces the weighted form (B),
  `max_Omega (c + t) >= 3N - 2 max delta`, to a two-level statement relative to a component
  `Z` of `{delta <= 1}`. That relative statement is false: take a thin tube along an L-shaped
  path that spans two coordinates, cut at its four wall crossings.

**Evidence** (`anneal.c`, `results.json`). Simulated annealing over usc functions on the
product cell complex (`6m + 1` cells per coordinate) found no counterexample:
- to (S), (T) or (B) at `N = 3` (`m = 1, 2`, `max delta <= 2`);
- to (B) at `N = 4` (`m = 1`, `max delta <= 1`).

The best score was always 1, one violation away from a counterexample. This is search
evidence only.

**Not settled.** (S) for `max delta >= 2` in dimension `N >= 3`, hence `ceil(N/2)` for
`N >= 5`. The first open case is `N = 5`, `beta = 5`: exclude `max delta = 2`.
