---
rg: 2
id: labbe-full-group-small-growth-actions-are-standard
kind: claim
title: Every action of Labbé's derived full group with subquartic Schreier growth consists of fixed points and standard orbits
distinct_from:
  full-group-confined-subgroups-are-finite-set-stabilizers: That classifies confined subgroups of a general full group; this turns small Schreier growth into confinement and then growth into a single point, for Labbé's group.
  minimal-free-sft-full-group-pattern-models-are-exact: That treats rule actions on validly coloured Z^2-sets; this treats abstract actions on sets, with no colouring, and finds that only the standard orbits can grow slowly.
artifacts:
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.** `Gamma = D([[Z^2 ~ Omega_U]])` for Labbé's shift, with a finite symmetric generating set `S`.
Let `Y` be a `Gamma`-set, not necessarily transitive, with `sup_y |B_k(y)| <= f(k)` for all `k`, where
`f(k) = o(k^4)`. Here `B_k(y)` is the ball in the Schreier graph.

**Statement.** Every `Gamma`-orbit in `Y` is either a single fixed point, or `Gamma`-isomorphic to the
`Z^2`-orbit of some `x ∈ Omega_U` with its standard action `u -> u + c_g(sigma^u x)`. In the second case
`St_Gamma(v) = St_Gamma(x)`.

**Mechanism.**
1. **Confinement.** Small growth excludes Cayley balls, so every point stabiliser is confined (Gromov:
   `Gamma` is infinite and simple, so it does not have polynomial growth).
2. **Classification.** Matte Bon's classification gives a finite `Q` with `St^0(Q) ≤ St(v) ≤ St(Q)`.
3. **Two points are too many.** Two points of `Q` would carry two independent quadratic walks, supported in
   disjoint clopen sets, and so give growth `>= c k^4`.
4. **One point.** For a single point, germs are trivial because the action is free, so `St(v) = St(x)`.

**Why it matters.** This is the extraction step toward LEF of `Gamma`. The small-growth limits of finite
models can only be standard tilings or fixed points. See `labbe-full-group-finite-small-growth-models-are-trivial`.

**Proof:** `labbe-full-group-small-growth-actions-are-standard-proof`.
