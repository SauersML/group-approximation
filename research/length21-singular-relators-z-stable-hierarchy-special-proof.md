---
rg: 2
id: length21-singular-relators-z-stable-hierarchy-special-proof
kind: route
title: Census at length 21 (n >= 3 empty by a length bound), top sZ by Collins plus Stallings pullbacks (also when A cap B is exceptional), level-one sZ, kbmag or C'(1/6), then Linton
target: length21-singular-relators-z-stable-hierarchy-special
requires:
  - linton-z-stable-one-relator-hierarchy-theorem
  - magnus-windows-are-linton-one-relator-towers
  - length19-singular-relators-z-stable-hierarchy-special
artifacts:
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/gen_singular21.py
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/gen_singular21_shard.py
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/gen_walk21.py
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/walk_validate.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/g19n2e9.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/gen21n1.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/gen21n2.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/rel821.txt
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/topsz.py
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/topsz_calib.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/top821.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/l1_821.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/sc821.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/kbrun.sh
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/kbretry.sh
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/kbretryrun.sh
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/kbhyp2.sh
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/autgroup_mwd.sh
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/kblargerun.sh
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/merge_kb.py
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/kbraw.out
  - experiments/one-relator-length21-singular-hierarchy-2026-09-18/kb821.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/magint.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/level1.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/kbhyp.sh
---

Date: 2026-09-18. A computation followed by cited theorems. The route is the one of
[[length19-singular-relators-z-stable-hierarchy-special-proof]], with one new step: the top
level no longer needs `A cap B` to be cyclic.

## 0. Census

`gen_singular21.py 21 n` with `EMAX = 9` and `LEXACT = 21` enumerates the syllable sequences
`((h_1, e_1), ..., (h_k, e_k))`: syllable `a^(e_j)` at height `h_j`, consecutive heights
different, cyclically. It keeps those of length `sum |e_j| + sum |h_(j+1) - h_j| = 21` that
satisfy the unit-Alexander, singular-extreme and unpeelable conditions of the claim. It
deduplicates them under the symmetry group (reflection of heights, reversal and inversion, sign,
rotation), and runs `census.cert_word` (the landed census search, budget 4000).

**Exponent bound.** For `n = 2` the heights cost at least 4 letters, so `sum |e_j| <= 17`.
- A level with at least two syllables and exponent sum in `{0, +-1}` has its largest `|e|` at
  most `(17 + 1)/2 = 9`.
- A level with a single syllable has exponent sum equal to that syllable. So it is the unit
  level, with `|e| = 1`.

So `EMAX = 9` is exhaustive. As a check, at length 19 `EMAX = 9` reproduces exactly the 52
candidates of the earlier census.

**Results.**
- `n = 1` (`gen21n1.out`): 660 candidates, all certified by the census search.
- `n = 2` (`gen21n2.out`): 841 candidates, 20 certified; the 821 OPEN ones are `rel821.txt`.
- `n >= 3`: none. This has a hand proof (below) and a machine check. `gen_walk21.py` is a
  second, structured enumerator: height walks first, then exponent tuples per level. It reuses
  `ok()` and `canon_seq()` verbatim. It reproduces the brute-force sets exactly (52 at length
  19 with `n = 2`; 660 and 841 at length 21), and it finds 0 candidates for `n = 3, 4, 5, 6` at
  length 21. It finds 96 for `n = 3` at length 23, which shows the check is not vacuous
  (`walk_validate.out`).

**Hand proof that `n >= 3` is empty at length 21.** Call the syllables at heights `0` and `n`
*extreme visits*, and the others *middle syllables*; let `V` and `M` count them. Cut the cyclic
walk at the extreme visits.
- **Segments.** A segment between visits to different extremes costs at least `n` letters of
  `t`. There are `2s` such segments, with `s >= 1`.
- A segment between two visits to the same extreme costs at least 2. It contains a middle
  syllable, because consecutive syllables have different heights. Let `q = V - 2s` be the number
  of such segments. Then `M >= q`, and `T := sum |h_(j+1) - h_j| >= 2sn + 2q`.
- **Extremes.** A singular extreme has at least 3 syllables, because two syllables with sum 0
  are peelable. Its exponents cost at least 4.
- An extreme of exponent sum `+-1` has at least 2 syllables (one syllable is peelable). Its
  exponents cost at least 3.
- Every middle syllable costs at least 1.
- **Unit level at an extreme.** Then `|w| >= 7 + M + T >= 7 + 2sn + 3q`, with
  `V = 2s + q >= 5`. The cases `s = 1, q >= 3`; `s = 2, q >= 1`; and `s >= 3` give
  `2n + 16`, `4n + 10` and `6n + 7`.
- **Unit level in the middle.** Then both extremes are singular, `V >= 6` and `M >= max(q, 1)`,
  so `|w| >= 8 + M + 2sn + 2q`. The same three cases give at least `2n + 20`, `4n + 14` and
  `6n + 9`.
- **Conclusion.** All six bounds are at least 22 for `n = 3` and increase with `n`. Now `|w|` is
  odd: `T` is even (closed walk), and `sum |e_j|` is odd (total exponent sum `+-1`). So `|w| >= 23`
  whenever `n >= 3`. For `n = 2` the same bounds give 19, which matches the length-19 census.

## 1. Top level

`G = B_0 *_psi`, `B_0 = <a_0, a_1, a_2 | W_0>` with `|W_0| = 11`, `A = F(a_0, a_1)`,
`B = F(a_1, a_2)`.

**Computing `D = A cap B`.** `topsz.py` repeats the immersion test of `magint.py`:
- rewrite `W_0` along an extreme letter `s` of exponent 0, giving a free vertex group `V`
  with a tracked basis;
- the subgroup `Y` generated by the copies of the letters of the Magnus subgroup containing
  `s` must satisfy `Y cap E+- = Y+-`, which makes the sub-line of groups immerse (Bass–Serre);
- then `A cap B`, conjugated by `s^h0`, equals `Y cap <u_h0>` inside the free group `V`.

It then computes a basis of that intersection from its Stallings graph (`I_basis`), and writes
each basis element both as a word in the `Y`-generators and as a word in the `u_h0`. It maps both
back to words in `a_0, a_1, a_2` and checks (an assert) that they give the same element of `V`.
The result is `D` written in the `A`-letters and, the same elements, in the `B`-letters.

**Reduction of `sZ` to free groups.** Linton (p. 23) defines:
- `A_0 = {[B_0]}`;
- `A_(k+1) = {[psi(A cap C^h)] : [C] in A_k, h in B_0}`;
- `sZ(psi)`, the supremum of `k+1` over those `k` for which `A_k` contains a non-cyclic class.

Now `A_1 = {[B]}`. Take `C <= B` and `h in B_0`. By Collins (Geom. Topol. Monogr. 14 (2008),
Thm 2), `hBh^-1 cap A` is cyclic unless `h = ab` with `a in A` and `b in B`. In that case

    hCh^-1 cap A = a (bCb^-1 cap A) a^-1 = a (bCb^-1 cap D) a^-1,

since `bCb^-1 <= B`. Cyclic classes have only cyclic descendants. So, up to conjugacy (which
does not change the depth at which non-cyclic classes stop), the non-cyclic part of `A_(k+1)` is
`{psi(bCb^-1 cap D) : b in B}` with `C` in the non-cyclic part of `A_k`.

This is exactly the forward iteration of `lintongraph.certify` on the free group `K = B`, with
partial map `D -> psi(D)`. Its depth-`j` states are the non-cyclic part of `A_(j+1)`. So
`sZ(psi) = f + 1`, where `(f, -) = certify(K = B, A' = D, B' = psi(D))['sZ']`. The same holds
for `sZ(psi^-1)`, with `K = A` and the map `D -> psi^-1(D)`.

In local letter ids, `psi` is the identity (`a_i` has id `i+1` in `A` and id `i` in `B`). Only
the `sZ` values are used, not certify's graph verdict (which asks for no BS subgroups, and that
is supplied by step 4).

**Calibration** (`topsz_calib.out`).
- `W_0 = [a_0,a_1][a_2,a_1]` has `D ⊇ <a_1, [a_0,a_1]>`, since `[a_0,a_1] = [a_1,a_2]`, so it is
  exceptional. `topsz.py` finds rank 2 and `sZ = (3, 3)`, the same as a hand-entered `D`.
- For free `B_0` with `D = F(a_1..a_(n-1))`, `n = 2, 3, 4`, it gives `sZ = n`, as expected for
  the standard shift on `F(a_0..a_n)`.

**Results** (`top821.out`).
- 713 relators: rank 1, so `sZ = (2, 2)` by Collins.
- 108 relators: rank 2, exceptional, with `sZ = (3, 3)`.

## 2. Level one

`level1.py` (unchanged from the length-19 route; `l1_821.out`). For each letter `s` of `W_0`
with exponent sum 0, it rewrites `W_0` along `s`. When the rewritten relator is primitive
(Whitehead-minimal of length 1), `V` is free on the tracked basis, and `lintongraph.certify`
computes `sZ(phi)` and `sZ(phi^-1)`. Every one of the 821 has such a letter with both values
finite: 607 via `a_0`, 195 via `a_1`, 19 via `a_2`, and the largest value is `(5, 5)`.

## 3. Hierarchy

By [[magnus-windows-are-linton-one-relator-towers]], the two rewritings give a one-relator tower
`X_2 -> X_1 -> X_0`. Its splittings are `psi` and `phi`, and `pi_1(X_2) = V` is free because the
last relator is primitive. So it is a hierarchy of length two, and it is Z-stable by 1 and 2.

## 4. No Baumslag–Solitar subgroups

`G` is hyperbolic, so it has no BS subgroup. The per-relator record is `kb821.out`
(`merge_kb.py`), and the raw logs are `kbraw.out`.

**Why kbmag success proves hyperbolicity.** `autgroup` computes a shortlex automatic structure,
and its last step, `gpaxioms`, verifies the axioms; the file `g.success` is written only when
they hold. `gpgeowa` then builds the geodesic word acceptor and the geodesic pairs machine. By
Papasoglu (Invent. Math. 121 (1995)), that success proves hyperbolicity. The calibration of
`kbhyp.sh` is in the length-19 route: it gives no false HYPERBOLIC on `Z^2`, `BS(2,3)` or
Baumslag–Gersten.

**How the 821 were settled.** The attempts ran in order, and each one only changes the search
parameters or passes to an isomorphic presentation. None of them changes what is verified.
- `kbhyp.sh`, default `autgroup`, 120 s per program: 625.
- `kbretry.sh`, the same on `w` with `a` and `t` renamed: 67.
- `kbhyp2.sh` with `autgroup -large`: 109.
- `-large` with the Knuth–Bendix word-difference cap raised from 512 to 8192: 14.
  - `autgroup_mwd.sh` is kbmag's `autgroup` script with one flag, `-mwd 8192`, added to the
    `-large` `kbprog` call. `gpmakefsa` and `gpaxioms` run unchanged.
- `C'(1/6)` (`sc821.out`), hyperbolic by Gromov (Lyndon–Schupp V.4): the remaining 6.

In all, 57 of the 821 are `C'(1/6)`; `merge_kb.py` prefers kbmag and uses `C'(1/6)` only where
kbmag had not succeeded.

## 5. Conclusion

Linton's Theorem 7.1 (3)⇒(1), from [[linton-z-stable-one-relator-hierarchy-theorem]], applies:
`G` is hyperbolic with a quasi-convex hierarchy. So `G` is virtually compact special (Wise,
Thm 13.3), hence linear, residually finite and sofic.

## Trust

- The top-level computation is new code. It is guarded by the equality assert and by the
  calibrations above.
- The Collins reduction is exact: it uses only Theorem 2's dichotomy and `bCb^-1 <= B`.
- The kbmag retries change only search parameters (time, `-large`, the word-difference cap) or
  rename the generators. Each success is still certified by `gpaxioms` and `gpgeowa`.
- The `n >= 3` emptiness is proved by hand. It is also checked by a second, independent
  enumerator that agrees with the brute force wherever both run.
- Everything else reuses code already landed with the length-19 route.
