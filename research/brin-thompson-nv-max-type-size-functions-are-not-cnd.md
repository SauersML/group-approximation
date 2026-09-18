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
  - research/artifacts/nv-cnd-and-germ-referee-audit-2026-09-18.md
  - experiments/nv-cnd-audit-2026-09-17/audit_linf_certificate.py
  - experiments/nv-cnd-audit-2026-09-17/audit_brick_lemma.py
  - experiments/nv-cnd-audit-2026-09-17/audit_calibration_1v.py
  - experiments/nv-cnd-audit-2026-09-17/audit_beta_range.py
  - experiments/nv-cnd-audit-2026-09-17/beta_one_fifth_certificate.json
  - experiments/nv-cnd-audit-2026-09-17/beta_three_twentieths_certificate.json
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
- **Not claimed:** index `0 < β < 3/20` (the referee audit of 2026-09-18 below lowered the threshold from `1/4`,
  with exact certificates). Grids up to `{−8..8}^3` show no failure at `β = 1/8` or `β = 0.1`. Misiewicz's theorem
  (functions of `‖x‖_∞` on `R^3` that are positive definite are constant) would extend item 2 to all `β > 0`, but it
  is not imported here.

## Attempts

### 2026-09-18, adversarial referee audit (`e2-w2-audit-nv1`, calibration) — SURVIVES, with two amendments

This claim landed ESTABLISHED in the previous wave with no referee stage. Full record:
`research/artifacts/nv-cnd-and-germ-referee-audit-2026-09-18.md`, Section A. Three lenses, no refuting step.
All checks below use `experiments/nv-cnd-audit-2026-09-17/`, which shares no code with the original lane.

- **Numerics re-derived from scratch.** Top eigenvalue of `‖x−y‖_∞^β` on the zero-sum subspace of `{−5..5}^3`:
  `+0.767118` at `β = 1/4` (a cnd kernel would give `≤ 0`). An integer zero-sum `c` was extracted from that
  eigenvector, the distance-class sums `N_d` computed as exact integers, and `Q = Σ_d N_d d^{1/4}` bounded below
  by **rational interval arithmetic** (`a_d ≤ d^{1/4} ≤ b_d` certified by `a_d^4 ≤ d ≤ b_d^4` in integers):
  `Q ∈ [+7.671182e11, +7.671182e11] > 0`, with no floating point in the final inequality. The lane's three stored
  certificates were re-verified the same way: every stored `N_d` reproduced exactly, every `Q0` confirmed positive.
  Item 4 reproduced: `Σ c_i c_j ‖x_i−x_j‖_∞ = 4` and `2^2204 > 2^2088·3^72`; an integer search shows `λ = 29`
  is the **smallest** scale at which the interval bound closes, so that constant is sharp for this method.
- **Item 1 re-derived independently.** A separate 2V implementation (canonicity by refining the diagram over the
  brick; `L` by exact cover over dyadic cells, not by the guillotine DP) gives `2^{‖w‖_∞} ≤ L ≤ 2^{|m|}+2^{|p|}+2^{|q|}`
  and `‖w‖_∞ ≤ D ≤ ‖w‖_∞ + 2` for all 125 elements with `|m|,|p|,|q| ≤ 2`, zero violations. Step 2's measure bound
  was checked over **all** canonical bricks (a superset of any diagram's bricks) for all 343 elements with
  `|m|,|p|,|q| ≤ 3`: zero violations, and tight.
- **Three inaccuracies of statement, none load-bearing.** (a) Step 0's `b_w^k` stacks the transferred letters in
  *reverse* order (`b_1^2(1a_1a_2 s, t) = (1 s, a_2a_1 t)`, verified); both uses only need the brick count and which
  input letters the second output depends on, so nothing changes. (b) Step 2's bound is about `W = B ∩ P`, not about
  the diagram brick `B`: for `w = (0,0,q)` the brick `[0] × C` is canonical, meets `[00] × C`, and has depth `1 < 2`.
  The route's own `u'_1 = the longer of u_1 and "1"` is the correct quantity and survives; dropping the prime produces
  a spurious counterexample. (c) Nothing else.
- **Amendment 1 (free strengthening).** The `+ M(1 − δ_e)` clause is redundant: in Step 5.2 the perturbation enters
  only as the constant `−M Σ c_x^2`, which is divided by `G(λ) → ∞`. The same holds for **any** bounded
  `b: nV → R`, whose contribution is at most `sup|b| (Σ_x |c_x|)^2`. So item 2 may be stated as "`ψ + b` is not cnd
  for every bounded `b`", which is what one wants against Haagerup, where a candidate proper cnd function is only
  pinned down up to a bounded error.
- **Amendment 2 (threshold lowered).** By Step 4, one certificate at index `β_0` kills all `β ≥ β_0`, so the `1/4`
  was only the reach of the grid the lane searched. Scanning intermediate indices: the first positive grid is
  `k = 4, 5, 6, 7` for `β = 1/4, 1/5, 7/40, 3/20`. Two exact certificates are stored:
  `beta_one_fifth_certificate.json` (`β = 1/5` on `{−5..5}^3`, `Q ≥ 5.71884e10`) and
  `beta_three_twentieths_certificate.json` (`β = 3/20` on `{−7..7}^3`, `Q ≥ 8.83909e10`), both by the same rational
  interval arithmetic. **Items 2 and 3 therefore hold verbatim with `1/4` replaced by `3/20`.** `β = 1/8` and
  `β = 0.1` remain at `0` through `{−8..8}^3`; the limit is computational, and Misiewicz's theorem is still the
  clean one-step route to all `β > 0`.
- **Calibration — the argument does not prove too much.** The decisive test is 1V, which has Haagerup (Farley).
  In `V` two cylinder partitions refine to `a + b − 1` pieces, so `L(gh) − 1 ≤ (L(g)−1) + (L(h)−1)` and leaf count
  grows only linearly: verified on 400 random pairs, and for three disjoint-support copies of `x_0` in `V` the exact
  value is `L(g(w)) = ‖w‖_1 + 6` on `{−4..4}^3` (leaf count additive over the pieces in 720 of 729 cases, the nine
  exceptions being the degenerate exponent-0 merges). So in 1V `log L(g(w)) = log ‖w‖_1 + O(1)`, slowly varying,
  index 0 — exactly the case item 2 excludes. For `n ≥ 2` two brick partitions refine to `a·b` pieces and the baker
  map attains it; that single line is the whole difference. The same argument covers SFT full groups and
  Nekrashevych groups, which act on a one-dimensional Cantor set. Inside `nV` the obstruction is also not too
  strong: `log D` is a *proper* index-0 function, so item 2 does not exclude a proper cnd function of that shape,
  and the claim does not say it does.
