---
rg: 2
id: thompson-f-monomial-doubling-ratio-is-a-finite-computation
kind: claim
title: For a homogeneous set of positive monomials of Thompson's F, the best expansion ratio in each degree is attained inside one explicit finite universe
distinct_from:
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that says doubling of some monomial set is equivalent to non-amenability; this reduces the doubling ratio of a given set in a given degree to a finite optimization and records exact values.
  thompson-f-moment-data-cannot-certify-nonamenability: that concerns closed-walk counts, which only bound the spectral radius from below; this concerns expansion of monomial sets in the positive monoid, where a finite set can certify a positive answer to P_(d,m).
artifacts:
  - research/artifacts/thompson-f-monomial-doubling-2026-09-13.md
---

**ESTABLISHED** through `thompson-f-monomial-doubling-ratio-finite-universe-proof`
(direct proof plus exact computation; not independently reviewed; no priority claimed).

Let `M` be the positive monoid of `F`, `M_D` its normal forms `x_(i_1) ... x_(i_D)` of degree `D`,
and `M_(D,L) ⊆ M_D` those with all letters `<= L`. Let `S ⊆ M` be a finite set of normal forms
`s = x_(s_1) ... x_(s_d)` of one degree `d`. Put

`Λ_S(D) = inf { |S Y| / |Y| : Y ⊆ M_D finite, nonempty }`, and
`R_S(D) = max over s ∈ S and 1 <= t <= d of (s_t + D + d - t)`.

1. `Λ_S(D) = min { |S Y| / |Y| : ∅ ≠ Y ⊆ M_(D, R_S(D)) }`. So `Λ_S(D)` is a rational number,
   and it is computed exactly by a minimum cut followed by Dinkelbach iteration.
2. `Λ_S` is nonincreasing in `D`.
3. `S` is not doubling (in the sense of `thompson-f-nonamenable-iff-some-monomial-set-doubles`)
   iff `Λ_S(D) < 2` for some `D`. Every nonzero pair in `K[S]` then has a common right
   multiple of degree `D`.

**Exact values** (`experiments/thompson-f/doubling_flow.cpp`, run on MSI; brute force over all
subsets agrees on every universe with at most 15 elements):
- **`S_(3,5)`** (the nine monomials of `P_(2,2)`): `Λ(1..7)` = `28/5, 9/2, 277/70, 835/231,
  2816/835, 4178/1307, 7501/2447, 22469/7610, 17279/6039, 481721/172855, 3305029/1213918, 3456957/1295921`, so
  `Λ(12) ≈ 2.6676`.
- **`S_(2,4)`** (`P_(2,1)`): `7/2, 3, 45/17, 263/107, 400/171, 973/435, 2941/1359, 4737/2245, 7929/3850,
  74419/36845, 159074/80215, 1081546/555319`. The first value below `2` is at `D = 11`
  (`thompson-f-p21-cardinality-certificate-in-degree-eleven`).
- **`X_2 = {x_0, x_1, x_2}`**: `9/4, 2, 31/17, 185/107, 571/342, 704/435, 2150/1359, 3491/2245,
  11779/7700, 55632/36845, 12224/8187, 459707/310984`.
- **`X_1 = {x_0, x_1}`**: `(D+2)/(D+1)` for `D <= 6`. This is computed, not proved in general.

Further sets (`X_3`, the fourteen monomials of `P_(3,1)`) and larger degrees are in the artifact.

The `X_2` column reproduces the survey's Theorem `xmy`(b) for `m = 2`: the first value below `2`
occurs at degree `3 = m(m+1)/2`.

**Scope.** These are exact finite optima, not asymptotics. No certificate for `P_(2,2)` exists
in degrees up to `12`. This is consistent with both answers to `thompson-f-is-amenable`: a
certificate could first appear at a higher degree, which would solve `P_(2,2)`, or never
appear, which would prove non-amenability. By the equivalence claim, no finite computation of
this kind can settle the second alternative.
