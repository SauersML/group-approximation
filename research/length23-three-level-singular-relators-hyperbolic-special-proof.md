---
rg: 2
id: length23-three-level-singular-relators-hyperbolic-special-proof
kind: route
title: Census at length 23 with four Magnus levels, per-relator choice of stable letter t or t a, top sZ by Collins plus Stallings pullbacks, level-one sZ with a primitive relator, kbmag, then Linton
target: length23-three-level-singular-relators-hyperbolic-special
requires:
  - linton-z-stable-one-relator-hierarchy-theorem
  - magnus-windows-are-linton-one-relator-towers
  - length21-singular-relators-z-stable-hierarchy-special
  - unit-alexander-singular-hidden-free-pieces-special
artifacts:
  - experiments/one-relator-length23-three-level-2026-09-18/w23n1.err
  - experiments/one-relator-length23-three-level-2026-09-18/w23n1.cert
  - experiments/one-relator-length23-three-level-2026-09-18/w23n2.err
  - experiments/one-relator-length23-three-level-2026-09-18/w23n2.cert
  - experiments/one-relator-length23-three-level-2026-09-18/w23n3.seq
  - experiments/one-relator-length23-three-level-2026-09-18/w23n3.err
  - experiments/one-relator-length23-three-level-2026-09-18/w23n4.err
  - experiments/one-relator-length23-three-level-2026-09-18/w23n5.err
  - experiments/one-relator-length23-three-level-2026-09-18/w23n6.err
  - experiments/one-relator-length23-three-level-2026-09-18/cert23.py
  - experiments/one-relator-length23-three-level-2026-09-18/w23n3.cert
  - experiments/one-relator-length23-three-level-2026-09-18/rebase.py
  - experiments/one-relator-length23-three-level-2026-09-18/rebased80.txt
  - experiments/one-relator-length23-three-level-2026-09-18/top96.out
  - experiments/one-relator-length23-three-level-2026-09-18/top_rebased80.out
  - experiments/one-relator-length23-three-level-2026-09-18/l1_96.out
  - experiments/one-relator-length23-three-level-2026-09-18/l1_rebased80.out
  - experiments/one-relator-length23-three-level-2026-09-18/kbhyp2.sh
  - experiments/one-relator-length23-three-level-2026-09-18/kb96.out
  - experiments/one-relator-length23-three-level-2026-09-18/kb29large.out
  - experiments/one-relator-length23-three-level-2026-09-18/merge23.py
  - experiments/one-relator-length23-three-level-2026-09-18/verdict23.out
  - experiments/one-relator-length23-three-level-2026-09-18/run23.sh
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/gen_walk21.py
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/topsz.py
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/topsz_calib.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/magint.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/level1.py
---

The tools are those of [[length21-singular-relators-z-stable-hierarchy-special]] and
[[unit-alexander-singular-hidden-free-pieces-special]], unchanged. The new ingredients are the
census at length 23 and the per-relator change of stable letter. `run23.sh` lists every command.

## 0. Census

`gen_walk21.py 23 n` is the landed structured enumerator of the length-21 route, run at length 23.
It is exhaustive for the slice at the given `(length, n)`, up to the symmetries `a -> a^-1`,
`t -> t^-1`, inversion and cyclic rotation.
- `n = 3`: 4669 height walks and 96 candidates (`w23n3.seq`, `w23n3.err`).
- `n = 4, 5, 6`: 11065, 13589 and 11563 walks, with no candidates.
- `n >= 7`: empty by a length bound. A singular extreme level has `k >= 3` syllables at distinct
  visits of the cyclic height walk, so the `t`-cost is at least `2n + 2(k - 1) >= 2n + 4`. The
  singular level carries exponent weight at least 4 (`1, 1, -2` is the least). The other extreme is
  unpeelable, so it has at least two syllables and weight at least 2. Each of the `n - 1` middle
  levels has weight at least 1. So `|w| >= 3n + 9`, which is at least 30 for `n >= 7`.

`cert23.py` runs `census.cert_word` on each candidate, with a fresh budget of 4000 calls per
relator. All 96 are OPEN (`w23n3.cert`). For the record, the same run certifies all 2226 `n = 1`
candidates (R1: an HNN extension over `Z` of a shorter one-relator group) and 80 of the 8041
`n = 2` candidates, and leaves 7961 OPEN (`w23n1.cert`, `w23n2.cert`). The `n = 2` relators are
not treated here.

## 1. Choice of presentation

Let `m >= 1`. The substitution `a -> a`, `t -> t a^(-m)` extends to an automorphism `alpha` of
`F(a,t)`, with inverse `t -> t a^m`. So `G = <a,t | w> = <a,t | alpha(w)>`, with the new stable
letter the image of `t a^m` in the old letters. `alpha` keeps the exponent sum of `t` at 0. The
Magnus rewriting of `alpha(w)` is a different HNN splitting of the same group, and its vertex group
and edge groups can differ from those of `w`.

`rebase.py fail80.txt 1 R` prints `alpha(w)` for `m = 1`, cyclically reduced (`rebased80.txt`). It
is applied to the 80 relators whose original top level is not certified (step 2). The statements
below only need some one-relator presentation of `G`, with `t`-exponent 0, in which steps 2 and 3
hold. It does not have to lie in the slice.

## 2. Top level

`topsz.py` is unchanged from the length-21 route and handles any number of levels:
- `B_0 = <a_0..a_n | W_0>`, `A = F(a_0..a_(n-1))`, `B = F(a_1..a_n)`;
- `D = A cap B` is computed inside the free vertex group of the rewriting of `W_0` along an extreme
  letter of exponent 0 (magint immersion test), with an equality assert;
- by Collins (Geom. Topol. Monogr. 14 (2008), Thm 2), `gBg^-1 cap A` is cyclic unless `g in AB`.
  So the non-cyclic part of Linton's `A_(k+1)` is the forward iteration of `lintongraph.certify` on
  the free group `B` with partial map `psi|D`. That gives `sZ(psi)`, and `sZ(psi^-1)` likewise.

The output tuple is `(sZ(psi), sZ(psi^-1), rank D, ...)`. The last two fields are certify's
verdicts with its inner depths `f' = sZ(psi) - 1` and `f'' = sZ(psi^-1) - 1`.

**Original presentation** (`top96.out`). 16 relators: rewriting along `s = a_3` works,
`rank D = 3` (exceptional, since `D` always contains `F(a_1,a_2)`), and `sZ = (4,4)`. The other 80
fail in the implementation. One extreme letter has non-zero exponent, and along the other either a
Magnus letter disappears (48, LETTER-ABSENT) or the height windows of the `N`-letters are disjoint
(32, N-SPLIT). That is a limit of the method, not a verdict about `sZ`.

**Rebased, `m = 1`** (`top_rebased80.out`). All 80 give finite values, and all still have `n = 3`.
- 48 have `D = F(a_1,a_2)` (rank 2, non-exceptional) and `sZ = (3,3)`. That is the value of the
  standard shift, as in the calibration `topsz_calib.out` (`sZ = n`).
- 24 have rank 3 and `sZ = (4,4)`.
- 8 have rank 3 and `sZ = (5,5)`.

## 3. Level one

`level1.py` is unchanged from the length-19 route. It rewrites `W_0` along each letter `s` of
exponent 0. If the rewritten relator is primitive (Whitehead-minimal of length 1), `V` is free on
the tracked basis, and `lintongraph.certify` computes `sZ(phi)` and `sZ(phi^-1)` by Stallings
pullbacks.
- Original presentation (`l1_96.out`): all 96 are ZSTABLE.
- Rebased (`l1_rebased80.out`): all 80 are ZSTABLE.

`merge23.py` uses the level-one letter from the same presentation as the top level. The counts are
in the table of the claim.

## 4. Hierarchy

Fix the presentation `P` of step 1, as `merge23.py` records it. By
[[magnus-windows-are-linton-one-relator-towers]] with `N = 2`, the Magnus rewriting along `t` (or
`y`) followed by the rewriting of `W_0` along `s` gives a one-relator tower `X_2 -> X_1 -> X_0`. Its
splittings are `psi` and `phi`, up to inversion. `pi_1(X_2) = V` is free, since the last relator is
primitive, so the tower is a hierarchy of length two. Steps 2 and 3 say that both splittings have
finite `sZ` in both directions, so the hierarchy is Z-stable. The level count `n = 3` does not
lengthen the hierarchy: the second rewriting already ends at a primitive relator.

## 5. No Baumslag–Solitar subgroups

`G` is hyperbolic, and hyperbolicity is an isomorphism invariant, so it is checked on the original
`w`. `kbhyp2.sh` (the length-21 script) runs `autgroup` and then `gpgeowa`. `g.success` is written
only when `gpaxioms` verifies the automatic structure, and success of `gpgeowa` then proves
hyperbolicity (Papasoglu, Invent. Math. 121 (1995)). The calibration against `Z^2`, `BS(2,3)` and
Baumslag–Gersten, with no false positives, is in the length-19 route.
- Default `autgroup`, 120 s per program: 67 (`kb96.out`).
- `autgroup -large`, 240 s: the remaining 29 (`kb29large.out`).

A hyperbolic group has no `BS(m,n)` subgroup.

## 6. Conclusion

`merge23.py` checks, for each of the 96, that the census is OPEN, that the top `sZ` and the level-one
`sZ` are finite in one common presentation, and that kbmag proves `G` hyperbolic. It prints
`certified 96 of 96` (`verdict23.out`). Linton's Theorem 7.1 (3)⇒(1), from
[[linton-z-stable-one-relator-hierarchy-theorem]], then says `G` is hyperbolic and has a
quasi-convex hierarchy. By Wise (Thm 13.3), `G` is virtually compact special, hence linear,
residually finite and sofic.

## Trust

- No new mathematical code. `topsz.py`, `level1.py`, `magint.py` and `kbhyp2.sh` are the landed
  length-19 and length-21 tools, run as is. The new scripts are `rebase.py` (a substitution plus
  free reduction), `cert23.py` (a loop over `census.cert_word`) and `merge23.py` (bookkeeping).
- The rebasing is an automorphism of `F(a,t)`, so it gives the same group. Only one presentation is
  used for each relator's hierarchy, and `merge23.py` checks that.
- The Collins reduction is used for `n = 3` exactly as for `n = 2`: Theorem 2 is stated for Magnus
  subgroups of any one-relator group.
