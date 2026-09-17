---
rg: 2
id: zaremsky-2-02-thompson-f-automatic
kind: claim
title: "Zaremsky Problem 2.2 resolved: is Thompson's group F automatic?"
root: true
distinct_from:
  thompson-f-is-automatic: that is the affirmative answer; this is the question, established by either answer
  thompson-f-is-not-automatic: that is the negative answer; this is the question, established by either answer
artifacts:
  - research/artifacts/zp-thompson-f-automatic-2026-09-13.md
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2 (Thompson groups),
Problem 2, verbatim: "Is F automatic?" The question is due to Guba and Sapir,
per Hauze's dissertation, Chapter 1.

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-02-by-yes` requires `thompson-f-is-automatic`.
- **No**: `zaremsky-2-02-by-no` requires `thompson-f-is-not-automatic`.

Never write a `requires: []` route into this claim.

## Reading

`F` is Richard Thompson's group: the orientation-preserving piecewise-linear
homeomorphisms of `[0,1]` with finitely many breakpoints, all at dyadic
rationals, and slopes powers of 2. It has the finite presentation
`< x0, x1 | [x0 x1^-1, x0^-1 x1 x0], [x0 x1^-1, x0^-2 x1 x0^2] >`
(Cannon–Floyd–Parry).

"Automatic" is in the sense of Epstein, Cannon, Holt, Levy, Paterson and
Thurston, *Word Processing in Groups* (1992): a regular language over a finite
symmetric generating set that maps onto the group and has the synchronous
fellow traveller property for accepted words whose endpoints are at distance 0
or 1 (their Theorem 2.3.5, as cited by Hauze).

Standard facts used:

1. automaticity does not depend on the finite generating set (Theorem 2.4.1);
2. an automatic group has an automatic structure with uniqueness (Theorem 2.5.1,
   ShortLex-minimal representatives);
3. in an automatic structure with uniqueness there is `N` with
   `|w| <= N |w̄| + N` for every accepted `w`. The pumping argument: if the unique
   representative of `g a` ran more than `N` steps past the length of the
   representative of `g`, two of those steps would share an automaton state and a
   position in the `K`-ball around `g`, and cutting the loop between them would
   give a second accepted word for `g a`.

So a positive answer is a regular language over `{x0^±1, x1^±1}` with
uniqueness and the fellow traveller property. A negative answer must exclude
every such language, including those whose words are only multiplicative
quasigeodesics.

Not asked: biautomaticity, asynchronous automaticity, or graph automaticity in
the sense of Kharlampovich–Khoussainov–Miasnikov.

## What is known

Sources read 2026-09-13; see the artifact for the full table.

- The Dehn function of `F` is quadratic (Guba, arXiv:math/0211395;
  `thompson-f-has-quadratic-dehn-function`). `F` is finitely presented and of
  type `F_∞` (Brown–Geoghegan 1984). So the classical obstructions (finite
  presentation, quadratic isoperimetric inequality, `F_∞`) are absent.
- Over the standard generators: there is no regular geodesic language and there
  are infinitely many cone types (Cleary–Elder–Taback, arXiv:math/0410616); `F`
  is not weakly geodesically automatic (Belk, as cited by Hauze); and near-geodesic
  languages are excluded, `thompson-f-has-no-near-geodesic-automatic-structure`
  (Hauze, arXiv:1801.01965, Theorem 1.1).
- `F` is 1-counter graph automatic (Elder–Taback, arXiv:1501.04313) and 3-counter
  graph automatic (Taback–Younes, arXiv:1501.04315). Neither bears on
  automaticity.

By fact 3, Hauze's theorem is the additive case over one generating set. The
multiplicative case, over all generating sets, is the whole problem.

## Attempts

- 2026-09-13 (lane z2-02-f-automatic): open ground on the "yes" side is
  structures whose words have unbounded additive excess over geodesic length. On
  the "no" side it is generating-set-free invariants that automatic groups might
  force. Landed:
  - `thompson-f-has-infinite-cohomological-dimension` (proved);
  - routes into `thompson-f-is-not-automatic` from
    `torsion-free-automatic-groups-have-finite-cd`, from
    `automatic-groups-have-contractible-rips-complexes` (through the finite-cd
    claim), and from `thompson-f-is-amenable` +
    `amenable-automatic-groups-are-virtually-abelian`. All of these prerequisites
    are open.
- 2026-09-13 (lane z4-01-amen-auto-rips, Problem 4.1):
  `thompson-f-has-no-contractible-rips-complex` (proved) and the route
  `thompson-f-not-automatic-if-amenable-via-rips`.
- 2026-09-17 (sw-104, compute-scout): the aim was to exclude the geodesic side of the
  "yes" search over every natural generating set. Landed
  `thompson-f-no-geodesic-combing-over-standard-generators`: over any finite `X`
  with `x0 ∈ X ⊆ {x_i}`, no automatic structure contains a geodesic for every element,
  so shortlex and geodesic structures are excluded. The proof is
  geodesic combing ⇒ almost convex, plus Horak–Stein–Taback Theorem 4.4.
  Finite SAT certificates are in `experiments/thompson-f-weighted-automatic-2026-09-17/`:
  `K_min = 4, 6` on `B_5, B_6` over `X_1`, and `K_min = 2, 4` on `B_4, B_5` over `X_2`.
  KBMAG shortlex over `X_1`, `X_2` and weighted orders timed out at 1200 s.
  Positive reweighting of `x0, x1` creates no new geodesics up to length 10.
  Dead: this route says nothing about additive excess `c > 0` off `X_1`, because the
  lemma lets paths leave `B(n)` by `c/2`. The open step is a Hauze-type argument over
  `X_n`, or a multiplicative-excess obstruction.
