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
- **2026-09-17 (swarm-0917-w5-nv-cocycle): central direction first; extractable spectra die.**
  Domination of the sup norm needs, at least, growth along `M·1_C`.
  - *Criterion, established* (`cantor-integer-maps-central-growth-criterion`).
    - Split along the spectrum of the central unitary `π(1_C)`. On each dyadic shell the
      cocycle is `(π(g) − 1)ξ_j`.
    - On the fixed part `b(1_C) = 0`, because `G` is perfect.
    - So `sup_M ψ(M·1_C) ∈ [2S, 4S]` with `S = Σ‖ξ_j‖²`.
    - Growth happens iff some representation has almost invariant vectors and no
      `1_C`-invariant vector.
  - *Kill, established* (`extractable-character-spectra-carry-no-almost-invariant-vectors`).
    - Suppose the spectral law lives on a `V`-invariant character set with an equivariant
      Borel extraction to `Prob(C)`.
    - Push the law forward. The moves `0↦00`, `0↦01`, first-letter swap force
      `max ‖π(h_i)η − η‖ ≥ 1/10`.
    - This kills finitely atomic characters, bounded phase variation (exponentials of signed
      measures) and every convergent `F`-variation. On that part,
      `sup_M ψ(M·1_C) ≤ 400 max_i ψ(h_i)`.
  - *Also dead.*
    - Quasimorphisms: all vanish on `A`.
    - Configuration-space characters: they are a special case of the kill.
    - Congruence quotients: `1_C` has finite order there.
  - *Open prerequisite* (`cantor-integer-maps-central-direction-has-relative-t`). Either
    produce almost invariant laws on scale-incoherent characters with `χ(1_C) ≠ 1`, or prove
    relative (T) for `(G, <1_C>)`. The latter proves `brin-thompson-2v-is-not-a-t-menable`
    through `cantor-integer-maps-not-a-t-menable-via-central-relative-t`.
