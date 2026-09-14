---
rg: 2
id: thompson-f-p22-x0-graded-sieve-certifies-no-pair
kind: claim
title: For every P_(2,2) pair over F_2 not settled by degree seven, both x_0-component pairs are equal or settled by degree seven, so the x_0-graded sieve certifies no pair
distinct_from:
  thompson-f-ore-x0-components-meet-no-later: that proves the component inequality for every field and every pair; this applies it to the unsolved list of the F_2 census and shows it excludes nothing
  thompson-f-p22-over-f2-exhaustive-degree-seven-census: that lists the 94329 pairs with no common right multiple of degree at most seven; this classifies their extreme x_0-components
artifacts:
  - research/artifacts/ideas-f-hyperbolic-2026-09-13.md
  - research/artifacts/ideas-f-hyperbolic-2026-09-13-data/sieve_output.txt
---
**ESTABLISHED** through `thompson-f-p22-x0-graded-sieve-census-proof` (exact computation on the census
data; not independently reviewed; no priority claimed).

**Setting.** The nine monomials `S_(3,5)` of Guba's Problem `P_(2,2)` split by the number of letters `x_0`:
- level 2: `x_0^2`;
- level 1: `x_0x_1, x_0x_2, x_0x_3`;
- level 0: `x_1^2, x_1x_2, x_1x_3, x_2^2, x_2x_3`.

Components `top`, `bot` and the degree `δ` are as in `thompson-f-ore-x0-components-meet-no-later`, over
`K = F_2`.

**Statement.**
1. Both elements of every unsolved pair have at least two nonzero levels. Equivalently, every pair of
   distinct nonzero single-level elements of `F_2[S_(3,5)]` has `δ <= 7`.
2. For each of the 94329 pairs with `δ > 7`, `(top(a), top(b))` and `(bot(a), bot(b))` are each either equal
   or a pair with `δ <= 7`. The counts are:
   - both component pairs equal: 166;
   - top equal, bottom settled: 26376;
   - top settled, bottom equal: 292;
   - both settled: 67495.
3. So the component inequality gives no lower bound above `7` for any unsolved pair. A proof that some
   `P_(2,2)` pair has no common right multiple over `F_2` cannot come from its extreme `x_0`-components; it
   has to use how the levels interact.

**Scope.** Only `F_2`, and only as far as the degree-seven census. It proves nothing about
`thompson-f-is-amenable` or `thompson-f-is-not-amenable`.
