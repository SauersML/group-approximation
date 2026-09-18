---
rg: 2
id: brin-thompson-nv-max-type-size-functions-are-not-cnd
kind: claim
title: "For n >= 2 no size function of nV that is asymptotically max-like on disjoint-support baker maps (log of the minimal brick count, its powers, diagram depth) is cnd, even after adding M(1 - delta_e)"
distinct_from:
  thompson-v-standard-cylinder-charts-are-commensurated: that shows the leaf count L - 1 is cnd on V, and so are its Bernstein transforms such as log L; this shows the same brick functionals stop being cnd on nV, even asymptotically, for n >= 2
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that kills wall counts, through growth along the distorted Callard-Salo element; this kills non-cubical size functionals such as log L, which grow like log N on distorted elements and pass that test, through an abelian subgroup where they grow like the l^inf norm
  brin-thompson-brick-charts-are-not-commensurated: that kills one commensurated set of charts; this kills cnd functions built from brick counts directly, whatever their origin
  cantor-integer-maps-sup-norm-is-cnd-dominated: that asks for a cnd function bounded below by F(sup-norm); this rules out cnd functions asymptotically equal to a regularly varying function of a sup-norm-type quantity, so a lower bound of that shape can only come from an l^1-type (additive over pieces) function
artifacts:
  - experiments/brin-thompson-cnd-2026-09-17/zcube_obstruction.py
  - experiments/brin-thompson-cnd-2026-09-17/zcube_linf_certificates.json
  - experiments/brin-thompson-cnd-2026-09-17/lib2v.py
  - experiments/brin-thompson-cnd-2026-09-17/verify_minbricks.py
  - experiments/brin-thompson-cnd-2026-09-17/certify_witness.py
  - experiments/brin-thompson-cnd-2026-09-17/cnd_census.py
  - experiments/brin-thompson-cnd-2026-09-17/lambda_growth.py
---

**ESTABLISHED** by `brin-thompson-nv-max-type-size-functions-are-not-cnd-proof`.

## Setting

- Let `n ≥ 2`. For `g ∈ nV`, `L(g)` is the minimal number of bricks in a brick diagram of `g`, that is, a
  partition of `C^n` into dyadic bricks on each of which `g` is a single brick map.
  `D(g)` is the minimal, over brick diagrams, of the largest total word length of a domain brick.
- For a word `w`, `b_w ∈ 2V ≤ nV` is the baker map on the brick `[w] × C^{n-1}`:
  `(w a s, t, z) ↦ (w s, a t, z)` for a letter `a`, and the identity off `[w] × C^{n-1}`.
- The maps `b_00`, `b_01`, `b_1` have disjoint supports, so they commute. For `w = (m, p, q) ∈ Z^3` set
  `g(w) = b_00^m b_01^p b_1^q`.

## Statement

1. **(max-like brick count)** For every `w ∈ Z^3`:
   `2^{‖w‖_∞} ≤ L(g(w)) ≤ 2^{|m|} + 2^{|p|} + 2^{|q|} ≤ 3·2^{‖w‖_∞}`, and
   `‖w‖_∞ ≤ D(g(w)) ≤ ‖w‖_∞ + 2`. In particular `w ↦ g(w)` is injective, and
   `log L(g(w)) = ‖w‖_∞ log 2 + θ` with `θ ∈ [0, log 3]`.
2. **(obstruction)** Let `G: [0,∞) → R` be positive on some `[λ_0, ∞)`, and `β ≥ 1/4` with `G(λ r)/G(λ) → r^β` as `λ → ∞`,
   uniformly on compact subsets of `(0, ∞)`. Let `ψ: nV → R` satisfy `ψ(g(w)) / G(‖w‖_∞) → κ > 0` as
   `‖w‖_∞ → ∞`. Then `ψ + M(1 − δ_e)` is not conditionally negative definite, for every `M ∈ R`.
3. **(corollaries)** None of the following, plus any `M(1 − δ_e)`, is cnd on `nV`, `n ≥ 2`:
   - `log L`;
   - `(log L)^β` for `β ≥ 1/4`;
   - `G(log L)` and `G(D)` for every `G` as in item 2, such as `(log L)^β log log L`;
   - `D`, `D^β` (`β ≥ 1/4`), and any `ψ` with `ψ(g) = G(D(g)) (1 + o(1))`.
   Numerically, `log L` passes the census on random subsets of `V × V` acting coordinatewise: the largest zero-sum
   eigenvalue is about `5e-15` on 80 elements. The obstruction uses the baker maps.
4. **(explicit finite witness for log L)** Let `x_1..x_5 = (−1,0,0), (−1,0,1), (0,−1,1), (0,1,1), (1,0,1)`,
   `c = (−2, −2, 3, 3, −2)` and `g_i = g(29 x_i)`. Then `Σ_{i,j} c_i c_j log L(g_i^{-1} g_j) > 0`. This follows from
   item 1 and the integer inequality `2^2204 > 2^2088 · 3^72`.

## Census data (supporting, same artifacts)

- **Exact finite witnesses from random subsets of 2V.** Found by `certify_witness.py`, with integer coefficients and exact
  arithmetic.
  - `L − 1`: 3 elements, `Q = 13148738`.
  - `√L − 1`: 4 elements in `V × V`, `Q ≈ 5.36e5`.
  - Symmetrized exponent-anisotropy integral `∫|a_x − a_y| + (g^{-1})`: 6 elements, `Q = 174273/2`.
  - Symmetrized exponent integral `∫(|a_x| + |a_y|) + (g^{-1})`: 10 elements, `Q = 180423/16`.
  - `log L`: 5 elements, one outside `V × V`, `Π L_ij^{c_i c_j} ≈ 8.96e15862 > 1`.
- **The exact DP for L.** The DP in `lib2v.py` uses the guillotine lemma. `verify_minbricks.py` checks it against an
  independent brute force on 325 elements, with no mismatch. Item 1 is checked by the DP for `|m|, |p|, |q| ≤ 3`.
- **Random census is blind to item 2.** On random sets of up to 320 elements of 2V (words of length ≤ 6), the largest
  zero-sum eigenvalue:
  - of `log L` grows: `2e-4, 0.0195, 0.127, 0.612` for `n = 40, 80, 160, 320`;
  - of `(log L)^{0.9}` is `0.294` at `n = 320`;
  - of `(log L)^{3/4}` and `(log L)^{1/2}` stays `≤ 1e-13`, although items 2–3 kill both.

  The failing configurations are the scaled `ℓ^∞` grids on `Z^3`, which random words do not reach.

## What survives, and where it dies

- **Invariant:** the asymptotic shape of `ψ` on the undistorted `Z^3` of disjoint-support baker maps.
- **Death step:** there `log L` and `D` are the `ℓ^∞` norm up to `O(1)`. `ℓ^∞`-type kernels on `Z^3` are not
  of negative type, and a scaling limit carries the certificate to `ψ`.
- **Untouched:** functions of slow variation (index 0), such as `log log L`. Their scaling limit is `1 − δ`, which is cnd.
  Also untouched: size functions that are additive over disjoint supports on this `Z^3` (`ℓ^1`-like).
  So a proper cnd function on `nV` must see the pieces of a diagram additively, not through their maximum.
- **Not claimed:** index `0 < β < 1/4`. Grids up to `{−7..7}^3` show no failure at `β = 0.1`. Misiewicz's theorem
  (functions of `‖x‖_∞` on `R^3` that are positive definite are constant) would extend item 2 to all `β > 0`, but it
  is not imported here.
