---
rg: 2
id: odd-congruence-vertex-sector-admits-no-exact-leak
kind: claim
title: Odd-congruence vertex data admits no exact leak, pinning the enemy to the prime two
distinct_from:
  far-sector-vertex-handled-edge-is-square-root: that exactifies the vertex restriction and reduces the far sector to the square-root edge; this eliminates an entire SECTOR of vertex representations (odd congruence level) from carrying the leak at all, regardless of edge behaviour.
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that proves co-density for exact representations of the whole group; this assumes exactness only of the VERTEX restriction and still kills the leak, using the normal closure of the edge subgroup instead of a global representation.
  no-exact-quasi-regular-leak: that is the open minimal core; this is its first unconditional sector exclusion, proved below.
---

Let `U_m` be microstates realizing an exact quasi-regular leak `(EQL1)`
over `Gamma = SL_2(Z[1/2])`, `Lambda = SL_2(Z)`, and let `rho_0` be the
exact representation HS-close to `U_m|_Lambda` supplied by
Gerasimova--Shchepin stability of the virtually free vertex group
(`far-sector-vertex-handled-edge-is-square-root`, step 1).  If `rho_0`
factors through a congruence quotient `SL_2(Z/m)` with `m` ODD (up to
the flexible corner), then the leak profile is forced to `1` at every
element: no exact leak exists over odd-congruence vertex data.

Consequently the enemy's vertex representation must carry essential
even-level (2-adic) or non-congruence content.  Combined with the
recorded convergence of all far-sector reductions, this localizes the
entire `SL_2` non-hyperlinearity battle at the prime `2` — the
square-root/solenoid direction — and proves that the co-density
mechanism is not merely unavailable to the enemy but actively forbids
it every congruence sector away from `2`.

## Attempts

- Proved below via the normal-closure squeeze; see the proof route
  `odd-congruence-vertex-sector-admits-no-exact-leak-proof`.  The one
  step that fails at `p = 2` is fullness of the edge image: the edge
  subgroup `Gamma_0(2)` has FULL image in `SL_2(Z/m)` for odd `m`
  (it contains the principal congruence subgroup `Lambda(2)`, which
  surjects by strong approximation), while mod `2^k` its image is a
  proper parabolic-type subgroup and every squeeze below breaks.  The
  even sector is therefore not an artifact of the method: it is
  exactly the solenoid sector where
  `bs14-unitary-representations-are-periodic-cycle-packets` lives.
