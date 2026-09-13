---
rg: 2
id: thompson-f-norm-bound-from-hhr-exact-moments
kind: claim
title: Simple random walk on Thompson's group F has Markov operator norm above 0.9015 (exact certificate on published moments)
distinct_from:
  thompson-f-random-walk-norm-certified-lower-bound: that certifies ||P|| > 0.880541 from closed-walk counts computed in this repository to length 30; this certifies the stronger bound 0.901532 from the exact moments to length 48 printed by Haagerup, Haagerup and Ramirez-Solano, re-deriving their published bound.
  thompson-f-moment-data-cannot-certify-nonamenability: that shows no finite list of counts proves ||P|| < 1; this is a lower bound only and says nothing about amenability.
artifacts:
  - experiments/thompson-f/hhr_certify.py
  - experiments/thompson-f/hhr_certify.json
  - experiments/thompson-f/hhr_certify_odd.py
  - experiments/thompson-f/hhr_certify_odd.json
  - research/artifacts/thompson-f-cogrowth-literature-pins-2026-09-13.md
---

**ESTABLISHED (computer-assisted, exact rational arithmetic on published data).** Let
`P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` act on `l^2(F)`. Then

    ||P|| > 225383/250000 = 0.901532,

equivalently the norm of `x_0 + x_0^{-1} + x_1 + x_1^{-1}` in `C*_r(F)` exceeds `3.606128`.

**Priority.** This is not new. Haagerup, Haagerup and Ramirez-Solano, *A computational approach
to the Thompson group F*, Internat. J. Algebra Comput. 25 (2015) 381–432, arXiv:1409.1486, state
`||A+A^{-1}+B+B^{-1}|| >= 3.60613` (arXiv source `ThompsonF.tex`, l.233–236), obtained by
orthogonal polynomials from their moments `m_n` for `n <= 24`. This node re-derives that bound with an
exact certificate and records exactly what it rests on.

**Data.** `c_{2j}` is the number of words of length `2j` in `x_0^{+-1}, x_1^{+-1}` trivial in `F`.
- `j <= 15`: computed in this repository (`experiments/thompson-f/out15.json`).
- `j = 16, ..., 24`: the column `m_n(h^*h)`, `h = A+B+A^{-1}+B^{-1}`, of HHR Table "The series of
  numbers for h=A+B+A^{-1}+B^{-1} (Case 2)", parsed from the arXiv source:

      4420986174041164, 50566377945667804, 581894842848487960, 6733830314028209908,
      78331435477025276852, 915607264080561034564, 10750847942401254987096,
      126768974481834814357308, 1500753741925909645997904

- **Cross-check.** The printed rows `n = 1..15` agree exactly with this repository's own counts
  `c_2..c_30` (`hhr_certify.json`, field `agree_with_repo_out15_j_le_15`).

**Trust surface.**
- Rows `16..24` are imported from the printed table and were not recomputed here.
- The certificate is one script (`hhr_certify_odd.py`), exact `Fraction` arithmetic, run on MSI
  with Python 3.10.10.

**Scope.** Lower bound only. By `thompson-f-moment-data-cannot-certify-nonamenability`, no finite
list of counts decides amenability. HHR's own extrapolation, `||A+A^{-1}+B+B^{-1}|| ≈ 3.87`
(`ThompsonF.tex` l.237–239), is not certified and is not claimed here.

Proof route: `thompson-f-norm-bound-from-hhr-exact-moments-proof`.
