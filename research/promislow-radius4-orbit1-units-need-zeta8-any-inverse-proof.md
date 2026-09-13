---
rg: 2
id: promislow-radius4-orbit1-units-need-zeta8-any-inverse-proof
kind: route
title: A syllable-length box, a complete case split over Q on the box, and the 16 points of case (0,1)
target: promislow-radius4-orbit1-units-need-zeta8-any-inverse
requires: [promislow-radius4-support-pairs-need-zeta8, promislow-inverse-has-equal-dihedral-syllable-length]
artifacts:
  - research/artifacts/promislow-radius4-census-box-2026-09-13.md
  - research/artifacts/promislow-radius4-census-box.py
  - research/artifacts/promislow-radius4-census-box-verify.py
  - research/artifacts/promislow-radius4-census-box-cases.py
---

Put `S = S_1` and `T = T_1`. The scripts read `census_pairs.json`, written by
mode `orbits` of `promislow-radius4-census.py`, where `S` is representative 1
and `T` is its inverse support over `F_2`.

**Step 0: one representative.** Each `phi in Phi` is an automorphism of `P`
(Step 1 of `promislow-radius4-support-pairs-need-zeta8-proof`). If `u` is a
nontrivial unit of `K[P]` supported in `phi(S)`, then `phi^(-1)(u)` is a
nontrivial unit supported in `S`, with inverse `phi^(-1)(u^(-1))`. So it is
enough to treat `S`.

**Step 1: the box.** Let `u in K[P]` be a unit with `supp(u) in S`. By
`promislow-inverse-has-equal-dihedral-syllable-length`,
`L_i^m(u^(-1)) = L_i^m(u) <= max_(h in S) l_i^m(h)` for `i = 0, 1, 2` and
every `m`. Every element of `P` is `(s, t)` with `s` one of the four signs of
`1, a, b, ab` and `t mod 2` fixed by `s`. Mode `bounds` of
`promislow-radius4-census-box.py` starts from the elements with translation
coordinates in a range around the one allowed by `m = 0`, and asserts that
the elements just outside it fail the `m = 0` condition. Farther out
`l_i^0` only grows, so no element of the box lies outside the range. It then
keeps the elements satisfying the conditions for `-40 <= m <= 40`. The result
`T'` contains the box, so `supp(u^(-1)) in T'`. Here `|T'| = 77` and
`T in T'`.

**Step 2: the case split on `(S, T')`.** This is Step 2 of
`promislow-radius4-support-pairs-need-zeta8-proof`, with `v` supported in
`T'`. Write `S = (g_0, ..., g_20)` in the script's order. For a nontrivial
unit `u` with inverse `v`, let `i < j` be the first two indices with
`u_i, u_j != 0`, scale `u` by `u_i^(-1)` and `v` by `u_i`, and put
`w = u_j^(-1)`. Then `(u, v, w)` is a `K`-point of the ideal `I_ij` generated
by the coefficients of `u v - 1` on the 330 cells of `S T'`, the `u_k` with
`k < i` or `i < k < j`, `u_i - 1` and `u_j w - 1`. Mode `cases 1 box 3600`
(job 598021) computed a basis of each of the 210 ideals with Singular
`slimgb` over `Q`. All 21 rows finished and no case reached the time limit.
Every case except `(0,1)` gave a basis containing a nonzero constant, which
rules out points over every field of characteristic zero. So `u_0 != 0` and
`u_1 != 0`, and the normalized point lies in `I_01`.

**Step 3: case `(0,1)` on `(S, T')`.**
`promislow-radius4-census-box-verify.py` (job 599042) recomputes `I_01` over
`Q` in `u_1, ..., u_20`, `v_h` for `h in T'`, and `w`. The ideal is
zero-dimensional of length 16. The characteristic polynomial of a random
linear form `L` on the quotient is squarefree of degree 16. So `I_01` has 16
distinct points over `Qbar`, and every coordinate is a polynomial in `L` over
`Q`. All 16 roots lie in `Q(zeta_8)`. The script evaluates the coordinates at
them, multiplies each `u` and `v` out in `Q(zeta_8)[P]` with the group law,
and finds `u v = 1` with `v` vanishing off `T` for all 16.

**Step 4: conclusion.** Let `u in K[P]` be a nontrivial unit with
`supp(u) in S`, and embed `K` in an algebraic closure. By Steps 1 and 2 its
normalized point is a point of `I_01` on `(S, T')`. By Step 3 it is one of 16
points, and each has `v` supported in `T`. So `supp(u^(-1)) in T`, and `u` is
a nontrivial unit on the pair `(S, T)`. By
`promislow-radius4-support-pairs-need-zeta8`, `K` contains a primitive eighth
root of unity. QED

**Trust surface.** `slimgb` over `Q` is exact. The emptiness of the other 209
cases on `(S, T')` rests on Singular finding a constant in the basis, with no
cofactor certificate. The length 16 and `cp` rest on the basis in Step 3. The
16 points are checked by multiplication in `Q(zeta_8)[P]`, independently of
any Groebner basis. Step 1 imports Theorem 3.1 of Craven--Pappas through
`promislow-inverse-has-equal-dihedral-syllable-length`. The support `S` comes
from Tabei's census through `census_pairs.json`.

## Attempts

- The same computation on representatives 0 and 2 to 6 (job 598021) did not
  decide every case. Representatives 0, 3, 4 and 5 left 1, 3, 3 and 4 cases at
  the 3600 s limit. Representative 2 was cancelled at 12 h after one row.
  Representative 6 ran out of memory at 24G after three timeouts, and its
  verify task hit the 6 h limit. Jobs 689435 and 689436 rerun the undecided
  parts with longer limits and more memory. See the artifact.
- The whole 155-element box of arXiv:2608.00103v1 as `T'` did not finish its
  first case in 30 minutes (job 584612, recorded in
  `promislow-radius4-support-pairs-zeta8-2026-09-12.md`). The per-support box
  here has 59 to 77 elements.
