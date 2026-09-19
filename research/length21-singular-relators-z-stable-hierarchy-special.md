---
rg: 2
id: length21-singular-relators-z-stable-hierarchy-special
kind: claim
title: Every length-21 unit-Alexander singular-extreme unpeelable one-relator group is sofic; the 821 two-level ones are hyperbolic and virtually special, including 108 with exceptional top Magnus intersection
distinct_from:
  length19-singular-relators-z-stable-hierarchy-special: that closes the 32 residual length-19 relators, all with cyclic top intersection A cap B (Collins, sZ = 2); here the relators have length 21, and 108 have a rank-two (exceptional) A cap B whose top sZ is computed by Stallings pullbacks inside the free Magnus subgroups.
  magnus-windows-are-linton-one-relator-towers: that proves the iterated Magnus windows are Linton hierarchies ending at a primitive relator; this applies it to a finite census.
  unit-alexander-singular-hidden-free-pieces-special: that certifies length-19 level-one pieces; this is the length-21 census, with the top level also certified.
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

ESTABLISHED (computation plus cited theorems, unreviewed). Proof:
[[length21-singular-relators-z-stable-hierarchy-special-proof]].

**Setting.** This is the length-21 analogue of the length-19 census closed by
[[length19-singular-relators-z-stable-hierarchy-special]]. The length-19 note ended by moving the
question to lengths at least 20, and to relators whose top Magnus intersection `A cap B` is
exceptional. Length 20 is empty: a unit Alexander polynomial with `t`-exponent 0 forces `|w|`
odd. So 21 is the next length.

The census `gen_singular21.py 21 n` (`EMAX = 9`, `LEXACT = 21`) lists, up to the symmetries
`a -> a^-1`, `t -> t^-1`, inversion and cyclic rotation, the cyclically reduced
`w in F(a,t)` of length exactly 21 such that:
- the exponent sum of `t` is 0;
- the Magnus rewriting has `n` levels;
- exactly one level has non-zero exponent sum, and it is `+-1` (unit Alexander polynomial);
- at least one extreme level is singular (exponent sum 0, at least 3 syllables);
- neither extreme is peelable.

`EMAX = 9` loses nothing: a level with exponent sum in `{0, +-1}` and at least two syllables has
largest `|e| <= (17 + 1)/2 = 9`, and a single-syllable level has `|e| = 1`. Each candidate is first
tried against the landed census certificate search (`census.cert_word`).

| levels `n` | candidates | census certificate | left open |
|---|---|---|---|
| 1 | 660 | 660 | 0 |
| 2 | 841 | 20 | 821 (`rel821.txt`) |
| `>= 3` | 0 | - | - |

There are no relators with `n >= 3` at length 21. The proof has a hand argument: the extremes need
at least 5 syllables, which forces `|w| >= 23` when `n >= 3`. A second, structured enumerator
(`gen_walk21.py`) checks it: it reproduces the brute-force sets exactly and finds 0 candidates
for `n = 3..6`.

## Theorem

For each of the 821 open two-level relators `w` in `rel821.txt`, the group `G = <a,t | w>` is
word-hyperbolic and virtually compact special. Hence it is linear over `Z`, residually finite,
and **sofic**.

With the census certificates, this settles the whole length-21 slice: every length-21 relator
with `t`-exponent 0, unit Alexander polynomial, a singular extreme and no peelable extreme gives
a sofic group.

## The four inputs

Here `G = B_0 *_psi`, with `B_0 = <a_0, a_1, a_2 | W_0>`, `A = F(a_0, a_1)`, `B = F(a_1, a_2)`
and `psi(a_i) = a_(i+1)`.

1. **Top level, finite `sZ(psi)` and `sZ(psi^-1)`, including the exceptional case**
   (`topsz.py`, `top821.out`).
   - 713 relators: `A cap B = <a_1>` is cyclic, so Collins' Theorem 2 gives `sZ = 2`.
   - 108 relators: `A cap B` has **rank 2**. This is the exceptional case
     `F(a_1) * Z` of Collins' Theorem 1, where the length-19 route had no bound.
     - `topsz.py` computes `D = A cap B` explicitly. It works inside the free vertex group of the
       rewriting of `W_0` along an extreme letter, with both expressions of each generator
       checked to agree.
     - It reduces the non-cyclic stabiliser classes to Stallings pullbacks
       `psi(b C b^-1 cap D)` inside the free group `B`, again using Collins' Theorem 2.
     - It finds `sZ(psi) = sZ(psi^-1) = 3` for all 108.
2. **Level one** (`level1.py`, `l1_821.out`). For every relator, some letter of `W_0` with
   exponent sum 0 gives `B_0 = V *_phi` with `V` free (primitive relator) and finite `sZ` in
   both directions: 607 via `s = a_0`, 195 via `a_1`, 19 via `a_2`, with values up to `(5,5)`.
3. **Hierarchy.** By [[magnus-windows-are-linton-one-relator-towers]], `V -> B_0 -> G` is a
   Linton one-relator hierarchy of length two, and it is Z-stable by 1 and 2.
4. **Hyperbolicity** (`kb821.out`, `sc821.out`).
   kbmag `autgroup` builds and verifies a shortlex automatic structure; `gpgeowa` then builds the
   geodesic word acceptor, and by Papasoglu this proves `G` hyperbolic. The per-relator record
   is `kb821.out`, and the raw logs are `kbraw.out`.

   | first attempt that succeeded | relators |
   |---|---|
   | default settings, 120 s (`kbhyp.sh`) | 625 |
   | `a` and `t` renamed (`kbretry.sh`) | 67 |
   | `autgroup -large` (`kbhyp2.sh`) | 109 |
   | `-large` with word-difference cap 8192 (`autgroup_mwd.sh`) | 14 |
   | `C'(1/6)`, so hyperbolic by Gromov (`sc821.out`) | 6 |

   All 821 are proved hyperbolic, and no relator is left unresolved.

By Linton's Theorem 7.1(3)⇒(1) ([[linton-z-stable-one-relator-hierarchy-theorem]]), `G` is
hyperbolic and virtually special.

## What this means for the lane

The exceptional top-level case is not an obstruction on this test bed. When `A cap B` has rank 2,
the top `sZ` is still finite (3), and it is computable by the same pullback machinery as level
one. The pipeline magint → Collins → Stallings `sZ` → kbmag → Linton now runs at length 21 with
no manual step. The whole length-21 slice is now closed.

The next slice is length 23, which is the first length with three-level relators:
`gen_walk21.py 23 3` gives 96 candidates, beside the `n <= 2` ones. The pipeline needs one
extension there: a three-step tower, with `sZ` checked at the middle level too.

The 14 relators that needed the raised word-difference cap suggest that kbmag will get slower
with length. At length 23 some relators may need a hyperbolicity certificate that does not go
through automatic structures.
