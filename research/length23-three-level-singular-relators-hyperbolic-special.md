---
rg: 2
id: length23-three-level-singular-relators-hyperbolic-special
kind: claim
title: The 96 three-level relators of length 23 in the unit-Alexander singular unpeelable slice are hyperbolic and virtually special, although none has a census certificate; 80 of them are certified only after the change of stable letter y = t a
distinct_from:
  length21-singular-relators-z-stable-hierarchy-special: that closes length 21, where no relator has three Magnus levels; here every relator has four levels a_0..a_3, and 80 of the 96 are certified only after rewriting in the basis (a, t a).
  length19-singular-relators-z-stable-hierarchy-special: that closes the 32 residual length-19 relators, all two-level; this is the first three-level case.
  magnus-windows-are-linton-one-relator-towers: that proves the iterated Magnus windows form a Linton hierarchy; this applies it to a finite census, in a presentation chosen per relator.
  unit-alexander-singular-slice-contains-non-rf-bs-groups: that shows the slice has members with Baumslag-Solitar subgroups from length 27 on, so the Linton route cannot close every length; this closes one piece of length 23, below that bound.
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

ESTABLISHED (computation plus cited theorems, unreviewed). Proof:
[[length23-three-level-singular-relators-hyperbolic-special-proof]].

**Setting.** `G = <a,t | w>` with `w` cyclically reduced of length 23 and `t`-exponent 0. Its
Magnus rewriting `W_0` in `a_h = t^h a t^-h` has levels `0..n`. The slice is the one of
[[length21-singular-relators-z-stable-hierarchy-special]]:
- exactly one level has non-zero exponent sum, and it is `+-1` (unit Alexander polynomial);
- at least one extreme level is singular (sum 0, at least three syllables);
- neither extreme level is peelable.

The length-21 note left length 23 open as the first length with three-level relators.

## Theorem

The census `gen_walk21.py 23 n` lists the slice up to the symmetries `a -> a^-1`, `t -> t^-1`,
inversion and cyclic rotation.
- For `n = 3` it has 96 classes. The landed census certificate search (`census.cert_word`, PEEL,
  PP, R1 and CYC, budget 4000) finds none for any of them (`w23n3.cert`, 96 OPEN).
- For `n = 4, 5, 6` it is empty (`w23n4.err`..`w23n6.err`). For `n >= 7` it is empty by the length
  bound `|w| >= 3n + 9` of the proof.

**All 96 groups with `n = 3` are hyperbolic and virtually compact special, hence linear, residually
finite and sofic.**

For each of them there is a presentation `P` of `G`, either `w` itself or `w' = w(a, t a^-1)`
(stable letter `y = t a`), such that in `P`:
1. the top Magnus splitting `G = B_0 *_psi` has `sZ(psi)` and `sZ(psi^-1)` finite (`topsz.py`);
2. `B_0` rewritten along a zero-exponent letter `s` is `V *_phi` with `V` free (primitive
   relator), and `sZ(phi)` and `sZ(phi^-1)` are finite (`level1.py`);
3. `G` is hyperbolic, certified by kbmag (`autgroup`, then `gpgeowa`; Papasoglu).

By [[magnus-windows-are-linton-one-relator-towers]] this is a Z-stable one-relator hierarchy of
length two, and Linton's Theorem 7.1 applies.

| presentation | top `(sZ(psi), sZ(psi^-1))` | `rank(A cap B)` | level-one letter | relators |
|---|---|---|---|---|
| `w` | (4,4) | 3, exceptional | `a_0` / `a_1` | 12 / 4 |
| `y = t a` | (3,3) | 2, `= F(a_1,a_2)` | `a_0` / `a_2` | 44 / 4 |
| `y = t a` | (4,4) | 3, exceptional | `a_0` / `a_1` | 14 / 10 |
| `y = t a` | (5,5) | 3, exceptional | `a_0` / `a_1` | 6 / 2 |

The rebased relators have length 25 to 31 and still four Magnus levels. Here `A = F(a_0,a_1,a_2)`,
`B = F(a_1,a_2,a_3)`, and `A cap B` always contains `F(a_1,a_2)`. So rank 3 means that `A cap B`
is exceptional (strictly larger, in the sense of Collins). 48 of the 96 are exceptional.

kbmag succeeded for 67 with default `autgroup` and for the other 29 with `autgroup -large`.
`merge23.py` checks, for each relator, that all three certificates hold in the same presentation.
It prints `certified 96 of 96` (`verdict23.out`).

## What is new

- **Three-level towers need no three-step hierarchy.** Level one of `B_0` already has a primitive
  rewritten relator, so the hierarchy has length two, although `W_0` has four levels.
- **The top `sZ` depends on the presentation.** For 80 relators, `topsz.py` cannot certify the
  original Magnus splitting. One extreme letter has non-zero exponent. Rewriting along the other
  extreme letter either loses a letter of the Magnus subgroup (48, LETTER-ABSENT) or gives disjoint
  height windows (32, N-SPLIT). These are limits of the implemented method, not obstructions. The
  automorphism `a -> a`, `t -> t a^-1` of `F(a,t)` keeps the `t`-exponent 0
  and gives a different Magnus splitting of the same group. That splitting is certified for all 80.
  Choosing the stable letter per relator is a cheap way to widen the census method.

## Not covered

- Length 23 with `n = 2` is not closed. The census certificates, with a fresh budget per
  relator, settle all 2226 one-level candidates (R1) but only 80 of the 8041 two-level ones, and
  leave 7961 OPEN (`w23n1.cert`, `w23n2.cert`). Those need the length-21 two-level pipeline at
  about ten times the length-21 volume.
- The method cannot reach every length: by
  [[unit-alexander-singular-slice-contains-non-rf-bs-groups]], from length 27 on the slice has
  members containing `BS(1,2)`, and from length 29 on members that are not residually finite.
