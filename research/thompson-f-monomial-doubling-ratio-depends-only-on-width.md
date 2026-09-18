---
rg: 2
id: thompson-f-monomial-doubling-ratio-depends-only-on-width
kind: claim
title: The optimal expansion ratio of a Guba monomial set on degree-D sets with letters up to L depends only on min(D, L - r)
distinct_from:
  thompson-f-monomial-doubling-width-bounds-degree: that proves constancy in the degree for D >= L-1 and the width bound with L-1; this conjectures the sharp threshold L - r, where r is the largest letter of S, and the identification with the unrestricted degree-(L-r) optimum.
  thompson-f-monomial-doubling-ratio-is-a-finite-computation: that proves the case D <= L - r (letters above D + r never help); this is the complementary range L - r < D < L - 1.
artifacts:
  - experiments/thompson-f-2026-09-17/width_degree_law.py
  - experiments/thompson-f-2026-09-17/width_degree_grid_s35.txt
  - experiments/thompson-f-2026-09-17/width_degree_grid_x2.txt
  - experiments/thompson-f-2026-09-17/width_degree_grid_s24.txt
  - experiments/thompson-f-2026-09-17/width_degree_s35_D10_scan.txt
  - experiments/thompson-f-2026-09-17/x2_optimal_D6_L7.txt
---

**OPEN** (conjecture with exact data).

Notation follows `thompson-f-monomial-doubling-width-bounds-degree`. Let `S` be one of the Guba
sets `S_(m+1,m+d+1)`, and let `r = m+d-1` be its largest letter. The conjecture: for all `D >= 1`
and `L >= r+2`,

`Λ_S(D, L) = Λ_S(min(D, L - r))`.

**What is proved.**
- Case `D <= L - r`. Here `R_S(D) = D + r`, so this is item 1 of
  `thompson-f-monomial-doubling-ratio-is-a-finite-computation`.
- Case `D >= L - 1`. Item 2 of `thompson-f-monomial-doubling-width-bounds-degree` makes the value
  constant in `D`.
- The open range is `L - r < D < L - 1`, which is nonempty only for `r >= 3`. There the
  conjecture says the value is already constant from `D = L - r` on.
- **The case `r = 2` is not settled by these two facts.** For `X_2` and `S_(2,4)` they give only
  `Λ_S(L-2, L) >= Λ_S(L-1, L)`, while the conjecture asserts equality.

**Data** (exact min cut, `experiments/thompson-f-2026-09-17/`):
- 0 mismatches with `L - r >= 2` on these grids:
  - `X_2` and `S_(2,4)`: all `D <= 9`, `L <= 11`;
  - `S_(3,5)`: all `D <= 9`, `L <= 10`, and `D = 10` at `L = 2..7, 9, 13`.
- The only mismatches are at `L = r+1`. There `Λ_S(D, r+1)` for `D >= 2` equals `11/2` for
  `S_(3,5)` (against `Λ(1) = 28/5`), `13/6` for `X_2` (against `9/4`), and `10/3` for `S_(2,4)`
  (against `7/2`).
- The optimal `X_2` sets at `L = 7` for `D = 5, 6, 8` all have 342 elements. The degree-6 set is
  the degree-5 set right-padded by `x_7`, so the optimum is exactly the padding of item 1.

**Consequence if true.** A small-doubling set for `P_(2,2)` needs a homogeneous component of
degree `>= 13` using a letter `>= 16`, instead of `>= 14`. The width profile `n ↦ Λ_S(n)` is then
the whole two-parameter table.

**Where the proof attempt stops.** Splitting by the last letter fails when `D+1 < L`: a letter
pushed through the whole word gets value `D+1`, which can be smaller than a later last letter.
For example, `x_1 · x_0^5 = x_0 · x_0^4 x_6`
(`experiments/thompson-f-2026-09-17/last_letter_fibres.py`). A proof needs a fibration that is
insensitive to letters in `(D, L]`, or an explicit injection from an optimal degree-`D` set into
degree `L - r`.
