---
rg: 2
id: full-shift-full-group-has-no-infinite-relative-fh-subsets
kind: claim
title: "Every infinite subset of the full-shift topological full group is unbounded for some cnd function on [[X]]; so no subgroup of [[X]] has an infinite relative-FH subset or an infinite relative-(T) subgroup, normal or not"
distinct_from:
  full-shift-topological-full-group-is-a-t-menable: that asks for one proper cnd function; this gives, for each infinite subset separately, a cnd function unbounded on it, and does not imply the Haagerup property
  full-shift-relative-fh-subsets-have-no-far-reading-density: that needs far reading at a positive density of positions (flat Følner vectors); this needs one far-read site (tent vectors) and kills the Θ = 0 survivors g_m and H_run
  wobbling-relative-fh-subsets-lie-in-displacement-balls: that confines relative-FH subsets to one ball B_K; this shows they are finite
  full-shift-full-group-has-infinite-normal-relative-t-subgroup: that claim is refuted by corollary 2 here
  full-shift-full-group-kazhdan-subgroups-are-finite: that concerns Kazhdan subgroups; corollary 2 here covers every relative-(T) pair (Γ, H) with Γ ≤ [[X]]
---

**ESTABLISHED (unreviewed).** Route: `full-shift-full-group-no-infinite-relative-fh-pair-tent-proof`.
Imports:
- For a unitary representation `π`, the function `g ↦ ‖π(g)ξ − ξ‖²` is cnd.
- Sums with nonnegative coefficients that converge pointwise, and pointwise limits, of cnd
  functions are cnd.

Corollary 2 also uses the standard equivalence between relative (T) and relative FH for a pair
(countable group, subgroup). This is the relative Delorme–Guichardet theorem, the same convention
as in `full-shift-relative-fh-subsets-have-no-far-reading-density`. Its easy direction, relative
(T) ⇒ relative FH, is the only direction used.

Lane proof by swarm-0917-w23-w23-nv-follow. No priority claimed.

## Setting

Notation is as in `full-shift-relative-fh-subsets-have-no-far-reading-density`:
- `X = {0,1}^Z` and `(σx)_n = x_{n+1}`;
- `g(x) = σ^{k_g(x)}x`, with window `w(g)`;
- `B_K = {‖k_g‖_∞ ≤ K}`.

A subset `Y ⊆ Γ` has **relative FH** in `Γ` if every cnd function on `Γ` is bounded on `Y`.

## Statement

1. **(Tent test.)** For every infinite `Y ⊆ [[X]]` there is a cnd function `ψ` on `[[X]]` with
   `sup_Y ψ = ∞`. It is built as a sum `Σ_j λ_j ‖π(g)ξ_j − ξ_j‖²`, where each `ξ_j` is a tent
   (a triangular, finitely supported vector) on one `σ`-orbit, or on the diagonal orbit of one pair.
2. **(Corollaries.)** For every `Γ ≤ [[X]]`:
   - every relative-FH subset of `Γ` is finite;
   - every subgroup `H ≤ Γ` such that `(Γ, H)` has relative (T) is finite, normal or not;
   - in particular every Kazhdan subgroup of `[[X]]` is finite.

   So `full-shift-full-group-has-infinite-normal-relative-t-subgroup` is **false**. The explicit
   survivors of the far-reading test, `{g_m}` and `H_run`, have no relative FH in `[[X]]`.
3. **(Γ_p.)** Suppose some pair `(Λ ⋉ A², A²)` has relative (T), with `A` infinite. Then
   `Λ ⋉ A²` does not embed in `[[X]]`, because `A²` would be an infinite relative-(T) subgroup.
   For `Γ_p = EL_2(F_p[t,t⁻¹]) ⋉ F_p[t,t⁻¹]²`, whether the pair has relative (T) is the input of
   `elementary-linear-semidir-pair-relative-t`. If that input holds, `Γ_p` is not a subgroup of
   `[[X]]`.

## What it kills

- **Class.** Every refutation of `full-shift-topological-full-group-is-a-t-menable` by a
  relative-FH (or relative-(T)) witness inside `[[X]]`: subsets, subgroups, normal subgroups,
  locally finite or not, in any `B_K`. Through the embedding `[[X]] ≤ 2V`, this also kills every
  refutation of `brin-thompson-groups-nv-are-a-t-menable` whose witness lies in a copy of `[[X]]`.
  The route `two-v-not-haagerup-from-full-shift-normal-relative-t` dies at its first step.
- **Invariant.** Recurrence of the `Z`-orbits. A point has zero capacity in `Z`: the tent of radius
  `R` has Dirichlet energy `≈ 2/R → 0`, while its peak value stays `1`.
- **Death step.** A relative-FH witness `Y` would need elements `y_j` with windows `w_j → ∞`
  (or displacements `D_j → ∞`).
  - Take two aperiodic points that differ at one site at distance `w_j` and that `y_j` moves by
    different amounts.
  - Every fixed `g` fails to see that site from the middle half of the pair's orbit, and slides the
    tent along the diagonal at cost `O(K_g²/R)`.
  - `y_j` splits the peak off the diagonal, at cost `≥ 1`.
- This subsumes, for `[[X]]`:
  - `wobbling-relative-fh-subsets-lie-in-displacement-balls`, via the single-orbit tent of part (b)
    of the route;
  - the far-reading test;
  - the relative-(T) local-finiteness kills.

## Not claimed

- **Not claimed: the Haagerup property of `[[X]]`.** The functions are built one subset at a time.
  A countable group whose infinite subsets are all cnd-unbounded need not have a proper cnd
  function; no implication is known to this lane.
- **The averaging barrier.** One would like a single function
  `ψ = Σ_n λ_n E_{pairs at scale n} ψ_{tent}`, averaged over pairs that split at distance `n`.
  - There are `2^{2n+1}` window-`n` patterns.
  - A sparse element such as `g_m` is detected only by pairs whose centre pattern lies in a
    cylinder of Bernoulli measure `≈ 2^{−2m}`.
  - So bounded-weight averaging gives `ψ(g_m) ≈ λ_m 2^{−2m}`.
  - Properness then needs `λ_m ≥ 2^{2m}`. With such weights, finiteness at the shift `σ`, or at any
    fixed element of positive displacement, requires the scale-`n` defect of `σ` to be `≪ 4^{−n}`,
    while the tent of radius `n` only gives `≈ 1/n`.

  A proper function must therefore choose pairs adapted to each element's pattern rather than
  average over patterns. That is the named remaining barrier for the positive direction.

## Attempts

- 2026-09-20 (swarm-0917-w23-w23-nv-follow): tent test proved (route above). A computational check
  of the defect bounds for `g_m`, `H_run` and `σ` is in
  `experiments/pair-tent-2026-09-17/check_pair_tent.py`.
