---
rg: 2
id: cantor-integer-maps-sup-norm-is-cnd-dominated
kind: claim
title: "Some conditionally negative definite function on C(C,Z) ⋊ V tends to infinity with the sup-norm of the map"
distinct_from:
  cantor-integer-maps-by-v-have-haagerup-property: that asks for a cnd function proper on all of C(C,Z); this asks only that it grow with ‖f‖_∞, ignoring supports and positions, and by brothier-problem-b-reduces-to-value-range-domination the two are equivalent.
  brothier-problem-b-reduces-to-value-range-domination: that is the established equivalence for every residually finite Γ; this is the remaining open condition for Γ = Z.
  cantor-integer-maps-by-v-are-not-a-t-menable: that denies the Haagerup property; its negation of this claim is the magnitude-only form of that denial.
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

Let `A = C(C,Z)` and `G = A ⋊ V`. The claim: there are a cnd function `ψ` on `G` and
`F: N → R` with `F(m) → ∞` such that `ψ(f) ≥ F(‖f‖_∞)` for every `f ∈ A`.

## Status

OPEN. By `brothier-problem-b-reduces-to-value-range-domination` it is equivalent to
`cantor-integer-maps-by-v-have-haagerup-property`, hence necessary for
`brin-thompson-groups-nv-are-a-t-menable` (via `C(C,Z) ⋊ V ≤ 2V`).

## Why it is the sharper target

- The positional part of properness (depth of the partition of `f`, number of
  pieces, where they sit) is already handled by congruence quotients
  `C(C,Z/N) ⋊ V ≤ V` and Farley's cube complex. Every recorded failure on the
  Haagerup node that came from codimension-one breaking or deep charts concerns that
  positional part.
- What is left is growth in magnitude, uniformly over supports. The test families are
  `M·1_U`, uniformly over proper clopen `U` (all `V`-conjugate to `M·1_{[0]}`), and
  the central element `M·1_C`.
- A cnd function that stays bounded on some `{M_k·1_{U_k}}` with `M_k → ∞` kills the
  construction; a subset with that property for all cnd functions refutes the claim
  and proves `brin-thompson-2v-is-not-a-t-menable`.

## Attempts

- **Sum of congruence truncations (dies, heuristic).** See the
  Attempts of `cantor-integer-maps-by-v-have-haagerup-property` (congruence truncation):
  in the fibre-first coding of `C(C,Z/N) ⋊ V ≤ V`, an element `h ∈ V` has about
  `N·carets(h)` carets while `M·1_C` has at most about `N` carets. Summing pulled-back
  Farley functions with weights that keep `Σ_N w_N ψ_N(h)` finite keeps
  `Σ_N w_N ψ_N(M·1_C)` bounded in `M`. A proof must use a structure whose cost of
  `V`-elements does not scale with the fibre size.
- **Restriction to `A` is not `V`-invariant, but is quasi-invariant.** For `h ∈ V`,
  `√ψ(h·f) ≤ √ψ(f) + 2√ψ(h)`. So the Lévy measure `ν_ψ` of `ψ|_A` on `Â` need not be
  `V`-invariant (which is impossible for non-atomic scaling families, artifact §3(e)),
  only invariant up to additive errors depending on `h`.
