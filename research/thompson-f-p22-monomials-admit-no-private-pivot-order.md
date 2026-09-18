---
rg: 2
id: thompson-f-p22-monomials-admit-no-private-pivot-order
kind: claim
title: No order on the positive monoid of F gives every element two private points in S_(3,5)·m; a 1092-element stubborn set in degree 7 blocks every order
distinct_from:
  thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs: that shows a private-pivot order would give doubling and non-Ore pairs, and rules out seven natural orders; this shows no order of any kind exists for S_(3,5), and characterizes existence for any S by a peeling computation.
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that computes the expansion ratio Λ_S(D), which stays above 2 for S_(3,5) through D = 12; this obstruction is strictly finer and already appears at D = 7, where Λ = 7501/2447 ≈ 3.07.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that is the doubling criterion for non-amenability; this kills one sufficient certificate for doubling, not doubling itself.
artifacts:
  - experiments/thompson-f-2026-09-17/stubborn_core.cpp
  - experiments/thompson-f-2026-09-17/verify_stubborn_core.py
  - experiments/thompson-f-2026-09-17/s35_stubborn_core_D7.txt
  - experiments/thompson-f-2026-09-17/stubborn_census.py
  - experiments/thompson-f-2026-09-17/stubborn_census.jsonl
---

**ESTABLISHED** through `thompson-f-p22-no-private-pivot-order-proof` (direct proof plus exact
computation, checked by two independent product implementations; not independently reviewed; no
priority claimed).

Notation as in `thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs`: `M` is the positive
monoid of `F`, `S ⊆ M` a finite set of normal forms of one degree `d`, `M_D` the degree-`D` layer,
`M_(D,L)` its normal forms with letters `<= L`, and for `w ∈ S M_D`, `N(w) = {m ∈ M_D : w ∈ S m}` (finite).
A *pivot order for `S`* is a total order on `M` under which every `m` has at least two private points.

**Definition.** A finite nonempty `Z ⊆ M_D` is *stubborn for `S`* if every `z ∈ Z` has at most one
`w ∈ S z` with `N(w) ∩ Z = {z}`.

1. **Obstruction.** If a stubborn `Z` exists, then under every total order on `M` the minimum of `Z`
   has at most one private point. So no pivot order exists for `S`, and items 1 and 2 of
   `thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs` have no instance for `S`.
2. **Exact characterization.** A pivot order for `S` exists iff no `M_D` has a stubborn subset. For
   finite `Y`, the union of all stubborn subsets of `Y` (its *core*) is found by greedy peeling:
   repeatedly delete a point with at least two successors whose surviving predecessor set is itself.
   So existence is decided by the family of finite computations `core(M_(D,L)) = ∅`.
3. **Finer than doubling.** If `|S Y| < 2|Y|` for a finite `Y ⊆ M_D`, then `core(Y) ≠ ∅`.
4. **`P_(2,2)`.** For the nine monomials `S_(3,5) = {x_i x_j : i <= j, i <= 2, j <= 3}`, `core(M_(7,10))`
   has 1092 elements, `|S_(3,5) Z| = 5304`, and every point of `Z` has exactly one `Z`-private successor
   (`s35_stubborn_core_D7.txt`). **Hence no pivot order exists for `S_(3,5)`.**
   - `core(M_(D,D+3)) = ∅` for `D <= 6`, and also `core(M_(6,16)) = ∅` and `core(M_(7,L)) = ∅` for `L <= 9`.
   - `core(M_(7,14))` is the same 1092 points.

**Census** (`stubborn_census.jsonl`): the least `D` with `core(M_(D,R_S(D))) ≠ ∅`.

| `S` | first `D` with a core | first `D` with `Λ_S(D) < 2` |
|---|---|---|
| `X_m = {x_0..x_m}`, `m = 1..6` | `m` | `m(m+1)/2` for `m <= 2` (survey Theorem `xmy`) |
| `S_(2,4) = X_1 X_2` | 4 | 11 |
| `S_(3,5) = X_2 X_3` | 7 | none through 12 |
| `X_3 X_4` (14 monomials) | 10 | not computed |
| `{x_0^2, x_1^2, x_2^2}` | 4 | not computed |
| `{x_a x_b x_c : a<=b<=c, a<=2, b<=3, c<=4}` | none through `D = 10` | not computed |
| all 21 degree-2 monomials, letters `<= 5` | none through `D = 9` | not computed |

**Scope.**
- This decides neither `thompson-f-is-amenable` nor doubling of `S_(3,5)`: `Λ_(S_(3,5))(7) ≈ 3.07`.
- It kills one certificate class completely for `P_(2,2)`: any triangular (order-based) private-pivot
  certificate. A doubling certificate for `S_(3,5)` would have to be non-triangular, for example a
  Hall-type 2-to-1 matching that is not induced by any order.
- The pattern `3m+1` for `X_m X_(m+1)` (`m = 1, 2, 3`) and `m` for `X_m` is computed, not proved.
