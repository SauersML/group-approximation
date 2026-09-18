---
rg: 2
id: thompson-f-monomial-doubling-width-bounds-degree
kind: claim
title: In the positive monoid of Thompson's F, a set whose normal forms use only letters up to L expands under any monomial set at least as much as the best set of degree L
distinct_from:
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that bounds the letters an optimal set of a given degree needs; this bounds the degree that helps a set with bounded letters, so the exact tables become width tables as well.
  thompson-f-folner-function-exceeds-every-tower: that lower-bounds the cardinality of Følner sets in F; this excludes a whole shape of sets, bounded-alphabet families of any size and degree, as small-doubling witnesses in the positive monoid.
  thompson-f-p22-monomials-admit-no-private-pivot-order: that rules out a pivot-order argument for P_(2,2); this is an expansion bound for all bounded-width sets under any monomial set.
artifacts:
  - experiments/thompson-f-2026-09-17/width_degree_law.py
  - experiments/thompson-f-2026-09-17/width_degree_grid_s35.txt
  - experiments/thompson-f-2026-09-17/last_letter_fibres.py
---

**ESTABLISHED** through `thompson-f-monomial-doubling-width-bounds-degree-proof`
(direct proof; not independently reviewed; no priority claimed).

Notation is from `thompson-f-monomial-doubling-ratio-is-a-finite-computation`. `M_(D,L)` is the
set of normal forms of degree `D` with all letters `<= L`. For a finite set `S ⊆ M` of
normal forms of one degree put `Λ_S(D,L) = min |S Y|/|Y|` over nonempty `Y ⊆ M_(D,L)`, and let
`Λ_S(D)` be the unrestricted optimum in degree `D`.

1. `Λ_S(D+1, L) <= Λ_S(D, L)` for all `D, L`.
2. `Λ_S(D, L) = Λ_S(L-1, L)` for every `D >= L-1`.
3. **Width bound.** For every finite nonempty `Y ⊆ M` whose normal forms all use letters
   `<= L`, `|S Y| >= Λ_S(min(D_Y, L-1)) |Y|`, where `D_Y` is the largest degree occurring in `Y`.
   If `Y` is homogeneous of degree `D`, the bound is `Λ_S(min(D, L-1))`.

**Obstruction.** Let `Y` be a small-doubling set for the nine monomials `S_(3,5)` of `P_(2,2)`,
that is, `|S_(3,5) Y| < 2|Y|`. The exact values `Λ_(S_(3,5))(D) > 2.66` for `D <= 12` then force
some homogeneous component of `Y` to have degree `>= 13` and to use a letter `>= 14`.

The invariant is the **width** `min(degree, largest letter - 1)`. A family has bounded width if it
grows only by raising the degree over a fixed alphabet `x_0, ..., x_L`. Examples are all
products `x_0^(a_0) ... x_L^(a_L)`, boxes and simplices in the exponents, and powers and
products of fixed positive words. Every such family has expansion ratio at least
`Λ_S(L-1) > 1`, so under the Donnelly set `X_2` its ratio stays away from 1. Every
bounded-width family dies at item 2. Once the degree reaches `L`, splitting by the last letter
turns a degree-`(D+1)` set into disjoint right translates of degree-`D` sets. The letters pushed
through the whole word are `>= D+1 >= L`, so they cannot imitate a last letter.

**Data.**
- Exact min-cut grids for `S_(3,5)` (`D <= 9`, `L <= 10`, plus `D = 10` at `L = 2..7, 9, 13`),
  for `X_2` and for `S_(2,4)` (`D <= 9`, `L <= 11`).
- The grids in `experiments/thompson-f-2026-09-17/` show 0 violations of items 1–3.
- They also support the sharper open law `thompson-f-monomial-doubling-ratio-depends-only-on-width`.

**Scope.** The bound is a property of `M` and of homogeneous components. A Følner set in `F`
enters `M` only after a large translation (proof of item 1 of
`thompson-f-nonamenable-iff-some-monomial-set-doubles`), and that translation raises letters. So
this excludes bounded-alphabet witnesses in `M`, not any class of subsets of `F` defined without
reference to `M`.
