---
rg: 2
id: length19-singular-relators-z-stable-hierarchy-special
kind: claim
title: All 32 residual length-19 singular-extreme relators (the 24 of class (D) and the 8 open) are hyperbolic and virtually special, hence sofic
distinct_from:
  length19-singular-relators-small-cancellation-sofic: that closes 14 of the 24 (D) relators by C'(1/6) on the whole relator; this closes all 32 by a two-level Z-stable one-relator hierarchy, with the top level controlled by Collins' theorem on Magnus intersections and BS-freeness by a kbmag hyperbolicity proof.
  unit-alexander-singular-hidden-free-pieces-special: that certifies level one of the Magnus piece for the 24 (D) relators and isolates them because the top level had no certificate; this certifies the top level (sZ = 2) for all 32 and replaces the rank-two graph test by hyperbolicity of G.
  row29-one-relator-group-is-hyperbolic-and-virtually-special: that is one length-15 group with a free rank-two Magnus piece; here the Magnus piece is not free and the hierarchy has length two.
  quasiconvex-hierarchy-piece-nonsingular-extremes-sofic: that needs both extreme exponent sums nonzero and a shift-dictionary argument; here one extreme is singular and no shift dictionary is used.
artifacts:
  - experiments/one-relator-top-magnus-intersection-2026-09-18/magint.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/calib_magint.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/calib_magint.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/level1.py
  - experiments/one-relator-top-magnus-intersection-2026-09-18/kbhyp.sh
  - experiments/one-relator-top-magnus-intersection-2026-09-18/rel32.txt
  - experiments/one-relator-top-magnus-intersection-2026-09-18/magint32.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/level1_32.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/kbhyp32.out
  - experiments/one-relator-top-magnus-intersection-2026-09-18/calib_kb.txt
  - experiments/one-relator-top-magnus-intersection-2026-09-18/calib_kb.out
  - experiments/one-relator-basis-search-2026-09-18/basis_search.py
  - experiments/one-relator-basis-search-2026-09-18/whitehead.py
---

ESTABLISHED (computation plus cited theorems, unreviewed). Proof:
[[length19-singular-relators-z-stable-hierarchy-special-proof]].

**Setting.** [[unit-alexander-singular-hidden-free-pieces-special]] leaves 32 of the 48
length-19 unit-Alexander singular-extreme relators without a certificate:
- the 24 of class (D), where the Magnus piece `B_0` satisfies (QC) and only nonsingularity (N)
  fails;
- the 8 open ones.

[[length19-singular-relators-small-cancellation-sofic]] closes 14 of the 24 by `C'(1/6)`.
`rel32.txt` lists all 32 (the 24, a blank line, the 8).

## Theorem

For each of the 32 relators `w`, the group `G = <a,t | w>` is word-hyperbolic and virtually
compact special. Hence it is linear over `Z`, residually finite, and **sofic**.

In particular the 10 (D) relators left open by the small-cancellation claim,

    AAtATattAATTatataTT AAtATattATTatataaTT AAtATattaTTatatAATT AAtATattaaTTatatATT
    AAtAtaTTattaTatAATT AAtaTattAATTatAtaTT AAtaTattATTatAtaaTT AAtaTattaaTTatAtATT
    AAttATATataTattaaTT AAttATaTatATattaaTT

and the 8 open relators

    AAtATattAATTattaTaT AAtATattATTattaaTaT AAtATattaTTattAATaT AAtATattaaTTattATaT
    AAtAtAATTattaTTataT AAtAtATTattaaTTataT AAtAtaTTattAATTataT AAtAtaaTTattATTataT

are closed. So the whole length-19 unit-Alexander singular-extreme residue of 48 is closed.

## The three inputs

In each case `t` has exponent sum 0, and the Magnus rewriting along `t` gives
`G = B_0 *_psi`, with:
- `B_0 = <a_0, a_1, a_2 | W_0>`, where `|W_0| = 9`;
- `A = F(a_0, a_1)`, `B = F(a_1, a_2)`, and `psi(a_i) = a_(i+1)`.

1. **Top level, `sZ(psi) = 2`.**
   - `magint.py` proves that `A cap B = <a_1>` in `B_0` (`magint32.out`: NONEXC for all 32).
   - It works inside the free vertex group of the next splitting of `B_0`, by a Stallings
     immersion test and a pullback.
   - Collins' theorem (*Intersections of conjugates of Magnus subgroups of one-relator
     groups*, Geom. Topol. Monogr. 14 (2008), Thm 2) says each `A cap hBh^-1` is then cyclic.
     So every class after the first is cyclic, and `sZ(psi) = 2`.
2. **Level one, finite `sZ`.** Rewrite `W_0` along a letter of exponent sum 0 to get
   `B_0 = V *_phi` with `V` free (the relator is primitive). `lintongraph.certify` then
   computes `sZ(phi)` by pullbacks (`level1_32.out`):
   - every one of the 32 has a letter giving a free `V` and finite `sZ <= 3`;
   - on the letter that `mmcert19.out` used, the 24 (D) relators give the same values,
     `(2,2)` or `(1,1)`;
   - the 8 open relators have a free `V` only for `s = a_0`, where the edge groups have rank 3
     and `sZ = (3,3)`.
3. **Hyperbolicity.** kbmag `autgroup` finds and verifies (with `gpaxioms`) a shortlex
   automatic structure. `gpgeowa` then builds the geodesic word acceptor, and by Papasoglu
   (Invent. Math. 121 (1995)) its success proves `G` word-hyperbolic.
   - `kbhyp32.out`: this succeeds for 30 of the 32.
   - The other 2 are `AAtataTAtaTTattAATT` and `AAttAATTatAtaTataTT`. `autgroup` exceeds
     its equation limit on both. Both are `C'(1/6)`, so they are hyperbolic by Gruber.
   - Hyperbolic groups contain no Baumslag–Solitar subgroup.

By Linton's Theorem 7.1(3)⇒(1) in [[linton-z-stable-one-relator-hierarchy-theorem]], the
length-two one-relator hierarchy `V -> B_0 -> G` is Z-stable, and `pi_1` has no BS subgroup.
So it is a quasi-convex hierarchy, and `G` is virtually special.

## Calibration

- **`magint.py`.**
  - On `W_0 = [a_0,a_1][a_2,a_1]` the intersection is exceptional, because
    `[a_0,a_1] = [a_1,a_2]` lies in `A cap B`. `magint.py` reports EXCEPTIONAL-CANDIDATE
    (rank 2) from both sides.
  - On `W_0 = a_0 a_2 A_0 A_2 a_1`, where `B_0` is free, it reports NONEXC
    (`calib_magint.out`).
- **`kbhyp.sh`.**
  - `Z^2 = <a,t | [a,t]>` is automatic but not hyperbolic, and `gpgeowa` does not finish.
  - `autgroup` fails on `BS(2,3)` and on Baumslag–Gersten (`calib_kb.out`).
  - So the pipeline reports no false HYPERBOLIC on these.

## What this means for the lane

No singular backward step of the shift dictionary is needed on this test bed. The
singular-extreme length-19 class is closed by the whole-group route (Magnus intersection,
then Collins, then Linton, then Papasoglu). Only standard hierarchy inputs are used. The
open question for the lane moves to lengths at least 20, or to relators whose top intersection
`A cap B` is exceptional. There Collins gives no bound and `sZ` has to be computed some other
way.
