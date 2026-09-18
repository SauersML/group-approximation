---
rg: 2
id: length19-singular-relators-small-cancellation-sofic-proof
kind: route
title: Certify C'(1/6) on the relator or on one Nielsen image, then cubulate and apply Agol
target: length19-singular-relators-small-cancellation-sofic
requires:
  - cprime-one-sixth-presentations-hyperbolic-and-torsion-free
  - hyperbolic-cubulated-groups-are-residually-finite
  - unit-alexander-singular-hidden-free-pieces-special
artifacts:
  - experiments/one-relator-basis-search-2026-09-18/smallcanc.py
  - experiments/one-relator-basis-search-2026-09-18/orbit_sc.py
  - experiments/one-relator-basis-search-2026-09-18/sc19.out
  - experiments/one-relator-basis-search-2026-09-18/orbit20.out
  - experiments/one-relator-basis-search-2026-09-18/kscan.py
  - experiments/one-relator-basis-search-2026-09-18/kscan.out
  - experiments/one-relator-basis-search-2026-09-18/calib.out
---

Date: 2026-09-18. A computation followed by classical theorems.

## 1. The certificate

`smallcanc.py` works as follows for a cyclically reduced `w`:
- It builds `R*`, the set of all cyclic permutations of `w` and `w^-1`. It asserts
  `|R*| = 2|w|`, so `w` is not a proper power and not conjugate to its inverse.
- It returns the maximum length of a common prefix of two distinct elements of `R*`.

That maximum is the maximal piece length. A piece is exactly a word `p` with two distinct
elements `p u`, `p v` of `R*`.

Classical `C'(1/6)` means every piece `p` of `r in R*` has `|p| < |r|/6`. With one relator,
this is `maxpiece < |w|/6`.

The run on `rest48.txt` gives `sc19.out`. For the 12 (D) relators of item 1 of the claim, the
maximal piece length is 3 and `|w| = 19`. Since `3 < 19/6 = 3.1667`, `C'(1/6)` holds.

**Hand check of one case, `w = AAtATatatAATTattaTT`.** The claim is that no subword of length
4 of the cyclic word `w` or `w^-1` occurs twice, while some subword of length 3 does. The
check counts cyclic subwords of `w` and `w^-1`:
- length 4: every count is 1;
- length 3: `tAT`, `Tat`, `ATT` and `att` each occur twice.

This agrees with the script.

## 2. The two Nielsen images

`a -> at`, `t -> t` is an elementary Nielsen automorphism `alpha` of `F(a,t)`. Hence
`<a,t | w> ≅ <a,t | alpha(w)>`, since `alpha` induces an isomorphism
`F/<<w>> -> F/<<alpha(w)>>`.

A direct substitution gives these cyclic reductions:

    alpha(AAtaTatAtATTattaaTT) = TATAtaatAATTatttataT   (length 20)
    alpha(AAtaTatAtaTTattAATT) = TATAtaatAtaTattATATT   (length 20)

The `orbit_sc.py` search found these as the words `TTTAttaaTAATatattATA` and
`TTTATAtaatAtaTattATA`, which are the canonical rotations of the words above or of their
inverses. A tracked recomputation composing the substitutions confirmed that
`canon(alpha(w))` equals the search hit (`check True`).

The maximal piece length of each image is 3 < 20/6, so each presentation is `C'(1/6)`.

## 3. From C'(1/6) to sofic

Let `G` be one of the 14 groups, with a one-relator `C'(1/6)` presentation `<a,t | r>`.
- `r` is not a proper power (`|R*| = 2|r|`). So by
  [[cprime-one-sixth-presentations-hyperbolic-and-torsion-free]] (Gruber, and classical),
  `G` is torsion-free and word-hyperbolic.
- By Wise (*Cubulating small cancellation groups*, GAFA 14 (2004)), a group with a finite
  `C'(1/6)` presentation acts properly and cocompactly on a CAT(0) cube complex. The same
  input is recorded in [[hyperbolic-cubulated-groups-are-residually-finite]] and, through
  Martin–Steenbock, in `cprime-one-sixth-presentations-are-hyperlinear-proof`.
- By [[hyperbolic-cubulated-groups-are-residually-finite]] (Agol 2013, with Haglund–Wise),
  `G` is virtually special, linear over `Z`, and residually finite.
- Residually finite groups are sofic.

Hence `G` is sofic. ∎

## 4. Why no singular backward step is needed here

`G` is residually finite, and the Magnus piece `B_0` embeds in `G`. So any finite set of
elements of `B_0` survives in some finite quotient `phi : G -> Q`. Put `x_j = phi(a_j)`. This
is a bi-infinite configuration over the finite alphabet `Q` that satisfies every window
`W_0(x_j, ..., x_(j+n)) = 1`. The shift dictionary's Lemma 2 is therefore met by a *periodic*
configuration, with no equation solved in either direction. This makes precise the sense in
which the singular backward step was avoidable on these 14.

It is consistent with (A) of [[unit-alexander-singular-hidden-free-pieces-special]]: every
such `Q` is non-solvable on `phi(B_0)`, because `N` is perfect.

## 5. The negative runs

- **`T(4)`.** `smallcanc.py` tests the definition in Lyndon–Schupp V.2 directly. `T(4)` fails
  if there are `r1, r2, r3 in R*` such that:
  - no two consecutive ones are mutually inverse;
  - each of `r1 r2`, `r2 r3`, `r3 r1` has a cancellation.

  All 48 relators fail `T(4)`, and a witness triple is printed for each. So `C'(1/4)-T(4)` is
  not available even where `C'(1/4)` holds.
- **Orbit search.** `orbit_sc.py 45 rest20.txt` runs a BFS under the 8 elementary Nielsen
  moves. It keeps canonical cyclic words of length at most 45, and at each word it tests
  `C'(1/6)`. For the 18 relators other than the 14 above, 168–240 words are reached and none
  is `C'(1/6)`. The best ratio is 4/19. This rules out classical small cancellation in that
  part of the orbit. It does not rule out longer orbit elements, or presentations with more
  generators.
- **Free pieces.** In every relator here the exponent sums are `(e_a, e_t) = (+-1, 0)`. The
  induced map on `H_1` must send `(+-1,0)` to a vector with second coordinate `0`. So its
  matrix is `[[+-1, k],[0, +-1]]`. Since `Out(F_2) -> GL_2(Z)` is an isomorphism (Nielsen),
  up to inner automorphisms and signs the new stable letter is `t a^k`.

  `kscan.py` recomputes the Magnus piece for `k in [-6,6]` and Whitehead-minimises it. For
  all 32 relators the minimal length is 9 or 7, independent of `k`, and never 1 (`kscan.out`).
  So no such base change gives a free vertex group for a one-level Linton certificate.

## 6. Calibration

- `BS(2,3) = <a,t | t^-1 a^2 t a^-3>` is not residually finite, and neither is
  Baumslag–Gersten. Both fail `C'(1/6)`, as do all of their Nielsen images of length at most
  30 (`calib.out`). A false positive there would have refuted the pipeline.
- 6 of the 16 relators certified virtually special by the independent Linton certificate
  (`linfree19.out` of the previous lane) are also `C'(1/6)`.
