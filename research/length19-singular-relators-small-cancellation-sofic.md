---
rg: 2
id: length19-singular-relators-small-cancellation-sofic
kind: claim
title: Fourteen of the 24 length-19 singular-extreme relators that fail only nonsingularity are C'(1/6) up to a Nielsen move, hence residually finite and sofic
distinct_from:
  unit-alexander-singular-hidden-free-pieces-special: that isolates the 24 relators whose piece satisfies (QC) and fails only (N), and certifies 16 others by a Linton graph certificate; this closes 14 of the 24 by classical small cancellation on the whole relator, with no hierarchy and no shift dictionary.
  quasiconvex-hierarchy-piece-nonsingular-extremes-sofic: that needs both extreme exponent sums nonzero; the relators closed here all have a zero extreme exponent sum.
  cprime-one-sixth-presentations-are-hyperlinear: that is the general theorem that finite C'(1/6) presentations are hyperlinear (through residual finiteness); this is the computation that 14 explicit singular-extreme relators, the minimal open cases of the shift dictionary, satisfy C'(1/6).
artifacts:
  - experiments/one-relator-basis-search-2026-09-18/smallcanc.py
  - experiments/one-relator-basis-search-2026-09-18/orbit_sc.py
  - experiments/one-relator-basis-search-2026-09-18/basis_search.py
  - experiments/one-relator-basis-search-2026-09-18/whitehead.py
  - experiments/one-relator-basis-search-2026-09-18/kscan.py
  - experiments/one-relator-basis-search-2026-09-18/rest48.txt
  - experiments/one-relator-basis-search-2026-09-18/d24.txt
  - experiments/one-relator-basis-search-2026-09-18/open8.txt
  - experiments/one-relator-basis-search-2026-09-18/rest20.txt
  - experiments/one-relator-basis-search-2026-09-18/sc19.out
  - experiments/one-relator-basis-search-2026-09-18/orbit20.out
  - experiments/one-relator-basis-search-2026-09-18/kscan.out
  - experiments/one-relator-basis-search-2026-09-18/calib.txt
  - experiments/one-relator-basis-search-2026-09-18/calib.out
---

ESTABLISHED (computation plus classical theorems, unreviewed). Proof:
[[length19-singular-relators-small-cancellation-sofic-proof]].

**Setting.** [[unit-alexander-singular-hidden-free-pieces-special]] lists the 48 length-19
relators `w` in `F(a,t)` that have unit Alexander polynomial and a singular unpeelable
extreme, and that no census certificate closes (`rest48.txt`). It splits them as:
- 16 closed by a hidden-free-piece Linton certificate;
- 24 in class (D) (`d24.txt`), where the piece satisfies (QC) and (S) and only nonsingularity
  (N) fails;
- 8 open (`open8.txt`).

The 24 were the proposed test bed for a singular backward step of the shift dictionary.

## Theorem

Let `R*` be the symmetrised closure of a cyclically reduced relator. A *piece* is a common
prefix of two distinct elements of `R*`, and `C'(1/6)` means every piece has length below
`|w|/6`.

1. **Twelve directly.** For 12 of the 24 (D) relators the longest piece has length 3 < 19/6
   (`sc19.out`), so `<a,t | w>` is `C'(1/6)`:

       AAtATatatAATTattaTT AAtATatatATTattaaTT AAtATatataTTattAATT AAtATatataaTTattATT
       AAtAtaTatAATTattaTT AAtAtaTataTTattAATT AAtAtATatATTattaaTT AAtaTatAtaaTTattATT
       AAtatATAtATTattaaTT AAtataTAtaTTattAATT AAttAATTatATatataTT AAttAATTatAtaTataTT

2. **Two after one Nielsen move.** `AAtaTatAtATTattaaTT` and `AAtaTatAtaTTattAATT` are not
   `C'(1/6)`, because they have a piece of length 4. The automorphism `a -> at`, `t -> t` of
   `F(a,t)` sends them to the length-20 relators

       TATAtaatAATTatttataT   and   TATAtaatAtaTattATATT

   up to cyclic permutation and inversion (`orbit20.out` prints canonical rotations). The
   longest piece of each is 3 < 20/6.

The 10 (D) relators left open are

    AAtATattAATTatataTT AAtATattATTatataaTT AAtATattaTTatatAATT AAtATattaaTTatatATT
    AAtAtaTTattaTatAATT AAtaTattAATTatAtaTT AAtaTattATTatAtaaTT AAtaTattaaTTatAtATT
    AAttATATataTattaaTT AAttATaTatATattaaTT

For these 14 relators, `G = <a,t | w>` is torsion-free and word-hyperbolic. By Wise it acts
properly and cocompactly on a CAT(0) cube complex. By Agol it is therefore virtually special,
hence linear over `Z`, **residually finite**, and **sofic**.

## Negative results

- **The other 18 do not yield.** These are the 10 remaining (D) relators and the 8 open ones.
  For each of them:
  - the longest piece is 4, so the relator is `C'(1/4)`;
  - `T(4)` fails, with a witness triple listed in `sc19.out`;
  - no relator in its `Aut(F_2)`-orbit of length at most 45 is `C'(1/6)`. The orbit is
    searched by elementary Nielsen moves, with 168–240 cyclic words per orbit (`orbit20.out`).

  So classical `C'(1/6)` and `C'(1/4)-T(4)` small cancellation are exhausted for them in that
  range.
- **No change of basis frees the piece.** In the 32 = 24 + 8 relators, `a` has exponent sum
  `+-1` and `t` has exponent sum 0. Since `Out(F_2) = GL_2(Z)`, up to inner automorphisms and
  signs the only bases in which the stable letter keeps exponent sum 0 are `t -> t a^k`. For
  `|k| <= 6` the Magnus piece stays non-primitive, with Whitehead-minimal length 9 or 7,
  constant in `k` (`kscan.out`). So a one-level Linton certificate with a free vertex group is
  not available in these bases.

## Calibration

- `BS(2,3)` (`TaatAAA`) and Baumslag–Gersten (`TAtaTatAA`) are not residually finite.
  Neither they nor any relator of length at most 30 in their `Aut(F_2)`-orbits is `C'(1/6)`
  (`calib.out`).
- Six of the 16 relators already certified virtually special by the Linton graph certificate
  are also `C'(1/6)`. That is consistent: both routes give virtually special.

## What this means for the lane

Within the minimal singular-extreme test bed, 14 of the 24 cases proposed for a new singular
backward step are closed without one. The group is residually finite, so its finite quotients
supply bi-infinite periodic configurations over a finite alphabet, and no backward equation
has to be solved. The residue of the length-19 unit-Alexander singular class is now 18
relators: the 10 (D) relators left here and the 8 open ones. All 18 are `C'(1/4)`, fail
`T(4)`, and have no `C'(1/6)` form of length at most 45.
