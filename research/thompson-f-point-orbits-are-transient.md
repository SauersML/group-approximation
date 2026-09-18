---
rg: 2
id: thompson-f-point-orbits-are-transient
kind: claim
title: "Every orbit of Thompson's F on (0,1) is transient, so every F-set whose stabilizer fixes an interior point is transient, and a recurrent orbit of any group containing F has locally fixed-point-free stabilizers"
distinct_from:
  f-dyadic-action-is-not-recurrent: that is transience of the single dyadic orbit (Mishchenko); this transfers it to every orbit (irrational, rational non-dyadic) by planting the deep part of the dyadic graph in each orbit, and derives the stabilizer constraint for all recurrent actions.
  thompson-f-recurrent-orbits-have-stabilizers-containing-f: that shows stabilizers of recurrent orbits contain F; this shows they fix no point of (0,1), even after intersecting with any rigid copy F_[p], which the rank-three test does not give.
  recurrent-orbits-force-every-z3-to-meet-the-stabilizer: that is the general rank-three test; this is a transience theorem specific to F on the interval, used through heredity and quotients.
artifacts:
  - experiments/f-extensive-2026-09-17/schreier_range.py
  - experiments/f-extensive-2026-09-17/schreier_range_output.txt
---

**ESTABLISHED.** **Setting.**
- `F` is the group of piecewise linear homeomorphisms of `[0,1]` with breakpoints in
  `Z[1/2]` and slopes in `2^Z`, the `F_(2,1)` of `thompson-f-character-simplex-citation`.
- Recurrence of an orbit of a finitely generated group is as in
  `recurrent-orbits-force-every-z3-to-meet-the-stabilizer`. It does not depend on the
  finite generating set.
- For a finite binary word `p`, `[p]` is the dyadic interval coded by `p`, and
  `ι_p : F → F` is the injective homomorphism that conjugates `g` into `[p]` by the affine
  map `[0,1] → [p]` and extends by the identity. `F_p := ι_p(F) ≅ F`.

**Statement.**
1. **All point orbits are transient.** For every `t ∈ (0,1)`, the orbit `F·t` is transient.
   The same holds for every orbit of `F` on the Cantor set `{0,1}^N` other than the two
   fixed points `0^∞` and `1^∞`.
2. **Interior fixed points force transience.** Let `Y` be an `F`-set and `y ∈ Y`. If
   `Stab_F(y)` fixes some `t ∈ (0,1)`, then `F·y` is transient.
3. **Local stabilizer constraint.** Let `G` be finitely generated, `θ : F → G` injective,
   and `G·y` a recurrent orbit. Then for every `y′ ∈ G·y` and every finite word `p`, the
   group `ι_p^(-1)(θ^(-1)(G_(y′)))` fixes no point of `(0,1)`. Equivalently,
   `θ^(-1)(G_(y′)) ∩ F_p` fixes no interior point of `[p]`. For `G = F` and `p` empty:
   the stabilizer of a point in a recurrent `F`-set fixes no point of `(0,1)`, so it has the
   single orbital `(0,1)`.

**Numerics.** On the Cantor model, `experiments/f-extensive-2026-09-17/schreier_range.py`
runs simple random walk from a dyadic point, from a random-tail point and from the
Fibonacci-word point. The mean range fraction `R_n/n` (8 runs, `n ≤ 2^16`, same step
sequence for all three) agrees within `0.01` at every scale, and exactly to three decimals for
`n ≥ 2^12`. The dyadic values are `0.139, 0.073, 0.045, 0.030, 0.018` at
`n = 2^8, 2^10, 2^12, 2^14, 2^16`. So the walk almost never reads the tail. The dyadic graph is transient, but its escape probability
is small and not yet visible at this scale. Item 1 explains why the profiles agree: every
orbit contains an isomorphic copy of the deep part of the dyadic graph.

**Consequences.**
- **Germ-groupoid route with recurrence.** Juschenko–Nekrashevych–de la Salle and
  Juschenko–Matte Bon–Monod–de la Salle get extensive amenability of the singular set from
  recurrence. For `F` acting on `[0,1]` or on the Cantor set, no orbit of interior points is
  recurrent (item 1). So that step is unavailable for every groupoid `𝓗` and every choice
  of singular set. Only extensive amenability proved without recurrence remains; for
  dyadic singular sets this is equivalent to the flagship.
- **Every natural `F`-set** is transient by item 2:
  - points, finite configurations and germs at interior points;
  - cosets of subgroups of a point stabilizer;
  - the Cantor set.
- **Recurrent actions must be exotic.** By item 3, stabilizers in a recurrent `F`-set
  meet every rigid copy `F_p` in a group with the single orbital `int [p]`. Continued in
  `f-functor-cocycles-need-an-exotic-recurrent-action`.

**Scope.** Elementary given Mishchenko transience (through
`f-dyadic-action-is-not-recurrent`) and Lyons–Peres. It says nothing about extensive
amenability of the dyadic action, which is not implied by recurrence and remains open.

Proof route: `thompson-f-point-orbits-are-transient-proof`.
