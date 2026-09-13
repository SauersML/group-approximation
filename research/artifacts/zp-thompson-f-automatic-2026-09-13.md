# Zaremsky Problem 2.2: is Thompson's group F automatic?

Lane z2-02-f-automatic, 2026-09-13. Root: `zaremsky-2-02-thompson-f-automatic`.

## Status

Open. The check was bounded: direct fetches of arXiv abstracts and of the Hauze
dissertation; the shared web-search budget was exhausted early in the session;
no MathSciNet or zbMATH. No claimed answer was found.

- Elder–Taback (arXiv:1501.04313), abstract: "It is not known whether
  Thompson's group F is automatic."
- Hauze (arXiv:1801.01965, dissertation 2017), Chapter 1: "Guba and Sapir posed
  the question of whether F is automatic. While we do not answer their question,
  we show a restriction on any potential automatic structure".
- Later work is covered by z-status-b's table
  (`research/artifacts/zp-open-status-sections-2-4-2026-09-13-part*.md`).

## Standard facts about automatic groups

Epstein, Cannon, Holt, Levy, Paterson, Thurston, *Word Processing in Groups*
(1992). Theorem numbers are as cited in Hauze's dissertation, Chapter 2.

- Thm 2.3.5: `G` is automatic iff there is a regular language `L` over a finite
  symmetric generating set with the synchronous fellow traveller property for
  pairs of accepted words whose endpoints are at distance 0 or 1.
- Thm 2.4.1: automaticity does not depend on the finite generating set.
- Thm 2.5.1: ShortLex-minimal representatives give an automatic structure with
  uniqueness.
- Pumping (argument recorded in the root): with uniqueness, `|w| <= N |w̄| + N`.
  So automatic structures may be taken to be multiplicative quasigeodesics, and
  no better in general.

## Known obstructions and why each fails for `F`

| Consequence of automaticity | Status for `F` | Source |
|---|---|---|
| finitely presented | yes | Cannon–Floyd–Parry |
| quadratic isoperimetric inequality | yes, Dehn function quadratic | Guba arXiv:math/0211395; `thompson-f-has-quadratic-dehn-function` |
| type `F_∞` | yes | Brown–Geoghegan 1984 |
| infinite torsion group, or nilpotent not virtually abelian | no, `F` is neither | classical |
| strongly geodesically automatic iff hyperbolic | `F` is not hyperbolic, so this excludes only that kind of structure | Papasoglu, as cited by Hauze |
| weakly geodesically automatic | no | Belk thesis Ch. 6, as cited by Hauze |
| near-geodesic languages over `x0, x1` | excluded | Hauze Thm 1.1; `thompson-f-has-no-near-geodesic-automatic-structure` |
| regular geodesic language over `x0, x1` | none; infinitely many cone types | Cleary–Elder–Taback arXiv:math/0410616 |

Counter-graph-automatic structures exist: 1-counter (Elder–Taback,
arXiv:1501.04313) and 3-counter from caret types (Taback–Younes,
arXiv:1501.04315). They use a symbol alphabet and counters, so they say nothing
about automaticity.

## The dimension program toward a negative answer

Established facts:

- `thompson-f-has-infinite-cohomological-dimension` (this lane): `F` is
  torsion-free and contains `Z^n` for every `n`.
- `torsion-free-contractible-rips-complex-gives-type-f` and
  `thompson-f-has-no-contractible-rips-complex` (lane z4-01).

Open general theorems, each implying that `F` is not automatic:

- `torsion-free-automatic-groups-have-finite-cd` (route
  `thompson-f-not-automatic-via-finite-cd`);
- `automatic-groups-have-contractible-rips-complexes`, which implies the previous
  claim and the Problem 4.1 answer
  `amenable-automatic-groups-have-contractible-rips-complexes`;
- given `thompson-f-is-amenable`: `amenable-automatic-groups-are-virtually-abelian`
  (route `thompson-f-not-automatic-via-amenable-rigidity`), or
  `amenable-automatic-groups-have-contractible-rips-complexes` (lane z4-01's
  route `thompson-f-not-automatic-if-amenable-via-rips`).

Partial evidence for the finite-cd claim: Kropholler's theorem gives it for
automatic groups in LH𝔉. A counterexample must lie outside LH𝔉, like `F`, and
if z2-08's open claim `every-torsion-free-f-infinity-group-of-infinite-cd-contains-f`
holds it must contain `F`. No torsion-free automatic group of infinite
cohomological dimension is known to this lane.

## Positive direction: what a structure must look like

- Over `{x0^±1, x1^±1}` any structure has words with unbounded additive excess
  over geodesic length (Hauze). Linear excess is allowed.
- The standard infinite normal form, rewritten with `x_i = x0^-(i-1) x1 x0^(i-1)`:
  right multiplication by `x0` rewrites indices along the whole word. Not
  expected to fellow travel; no proof recorded.
- Forest-diagram tours (Belk–Brown): a caret operation at the pointer can move
  the start of a canonical tour, the mechanism behind the failure of tour normal
  forms for lamplighter groups. Still plausible only if the tour order is chosen
  so that local changes affect a bounded suffix after reparametrization.

## Sharpest next targets

1. Literature: is a torsion-free automatic group of infinite cohomological
   dimension known, or is finite cohomological dimension of automatic groups a
   stated open question? Needs search tools this session lacked.
2. Rips contractibility at a fixed scale for automatic groups: find structures
   with additive fellow travelling at scale `d`, and decide which automatic groups
   carry one (coordinate with z4-01-amen-auto-rips).
3. Positive direction: a language whose words for `g` and for `g x0`, `g x1`
   differ only in a bounded suffix after synchronous reparametrization.
