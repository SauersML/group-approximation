---
rg: 2
id: brin-thompson-groups-nv-lack-property-t
kind: claim
title: "No Brin-Thompson group nV (n >= 2) has Kazhdan's property (T)"
---

For every `n >= 2`, the Brin–Thompson group `nV` does not have property (T):
it has an isometric affine action on a Hilbert space without a fixed point,
or equivalently a unitary representation with almost invariant vectors and no
invariant vector.

This is the "no" answer to the (T) part of Zaremsky Problem 2.7
(`zaremsky-2-07-brin-thompson-nv-haagerup-or-t`). Property (T) does not pass to
subgroups or overgroups, so the claim is per `n`.

## Attempts

- **From a-T-menability.** Immediate from `brin-thompson-groups-nv-are-a-t-menable`
  (route `brin-thompson-nv-lack-property-t-from-a-t-menability`).
- **Amenable action without finite orbits.** A (T) group acting on a set with
  an invariant mean has a finite orbit. Candidate `nV`-sets are orbits of
  points of `C^n` and coset spaces of fibration stabilizers
  `LC(C, V) ⋊ V`. For `V` on the orbit of an aperiodic point, the level
  function `|u| - k` of `u σ^k x` changes by bounded amounts but the level sets
  grow like `2^level`, so level-band Følner candidates fail by a constant
  fraction. No amenable candidate yet.
- **Unbounded commensurating action.** Any commensurated subset with unbounded
  `|gA Δ A|` would do (no FW, hence no (T)). The action must be
  infinite-dimensional, by `FW_infinity`. Constraint: in a commensurating
  action every cyclic subgroup has `|f^n A Δ A|` either bounded or linear in
  `n`, so the distortion element of Callard–Salo (arXiv:2208.00685) is elliptic
  in every such action.
- **Maharam extension (dies).** `nV` preserves the Lebesgue class on `C^n` with
  Jacobians in `2^Z`. On `C^n x Z` with the invariant measure `μ ⊗ 2^k` and
  `g(x, k) = (gx, k - log_2 J_g(x))`, the half-space `{k >= 0}` is
  commensurated, but its complement has finite measure. So the cocycle is
  bounded. Per-coordinate extensions on `C^n x Z^n` with half-spaces
  `{k_1 >= 0}` are not commensurated, because the transverse sums
  `Σ_{k_2} 2^{k_2}` diverge.
- **Finite-set sums (die).** `ψ = Σ_k w_k |g S_k Δ S_k|` over finite brick
  families `S_k` is bounded unless the `S_k` are almost invariant, and the
  chart action contains free orbits and scales depth by constant fractions.
- **Codimension-one objects.** Bricks, slabs, horizontal or vertical lines, and
  point orbits `D^n` all have infinitely many broken objects per element,
  because one coordinate can be short while the other is arbitrary.
