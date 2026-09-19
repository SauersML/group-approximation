# The second cuspidal projective chart has a small exact harmonic section

Date: 2026-08-11

## Outcome

The compact signed-coinvariant cellular calculation has now been repeated at
the next cuspidal prime, `p=61`.  It gives the exact rational complex

`Q^183 <- Q^480 <- Q^440 <- Q^150`                         `(P61-1)`

with boundary ranks

`182, 298, 140`.                                             `(P61-2)`

Both consecutive products vanish and

`dim_Q H_2=440-298-140=2`.                                  `(P61-3)`

Thus the rank-two cuspidal sector seen independently in the
Ash--Grayson--Green function model is reproduced in a second exact cellular
chart.

The harmonic discriminant is again cyclic:

`Q^#/(K intersect H) ~= Z/q_61 Z`,                           `(P61-4)`

where

`q_61=784027680124070571244902013018900874324624829344998811622894236133560467890375653648339615390452725402770059419298`.
                                                               `(P61-5)`

This order has `114` decimal digits, larger than the `83`-digit order at
level `53`.  Nevertheless, exact affine lattice reduction finds a modest
integral harmonic section.

## Exact harmonic metric

In a Gauss-reduced basis, write `G_H=(1/q_61)[[a,b],[b,c]]`, with

`a=97820187344269663377715317644639474143710242630887848406910237931008685950609211986741628687668122612430743948609`,

`b=6341016500041665942461651540705341606108586878369578414219727363053859476238879789165927698545616717842639681887`,

`c=327481707558530172141936273258164582168885284351423489831325060580670153770614187205777952073817157480161455382829`.
                                                               `(P61-6)`

The shortest nonintegral harmonic vector has

`||u_1||^2=a/q_61=0.12476624209082751...`,
`||u_1||=0.3532226522900641...`.                              `(P61-7)`

It has full order `q_61`.  Unlike the level-`53` shortest vector, it is not
below the spherical localization threshold: the largest squared
degree-three boundary-template norm is `28`, and

`28a>q_61`.                                                   `(P61-8)`

Thus the second cusp does not continue the possible denominator-collapse
trend.  Its dual systole is larger than the level-`53` value
`0.2670563781...`.

## Exact integral section

The raw HNF lifts have coefficients of order `10^35`.  Saturating the
rank-`298` range lattice and applying exact LLL/BKZ/Babai reduction produces
two verified integral lifts with squared norms `17` and `10`.  Every
nonzero coefficient is `+1` or `-1`; their overlap is `-3`.  Consequently

`G_Z=[[17,-3],[-3,10]].`                                     `(P61-9)`

Exact cycle pairings verify their harmonic projections, and the
degree-three boundary annihilates both lifts.  The generalized squared
singular values of the section are

`22.239342479055036...`, `139.0902358480397...`.             `(P61-10)`

Equivalently, they are the roots of the exact rational polynomial stored in
`experiments/projective-cellular-p61-section.json`.  Hence

`||s_61||=11.793652354043665...`.                             `(P61-11)`

This is a rigorous upper bound for the full free rank-two harmonic lift
constant in the compact level-`61` metric.  No optimality claim is made for
the two chosen lifts.  Exact binary coset-leader optimization proves that
every integral lift of the first basis class has squared norm at least `5`
(the displayed lift has squared norm `17`).  It follows that

`kappa_Sigma,61>=sqrt(5q_61/a)=6.330477286783821...`.         `(P61-12)`

Together with `(P61-11)`,

`6.330477286783821...<=kappa_Sigma,61`
` <=11.793652354043665...`.                                  `(P61-13)`

The important family-level comparison is therefore

| level | harmonic rank | dual systole | certified section norm |
| ---: | ---: | ---: | ---: |
| `53` | 2 | `0.2670563781...` | `7.4901774197...` |
| `61` | 2 | `0.3532226523...` | `11.7936523541...` |

Neither denominator collapse nor explosive numerator growth occurs in the
second exact cusp.  Two levels do not prove a uniform theorem, but they
replace the single-chart observation by a genuine replicated phenomenon.

## Certificates and scope

The exact files are:

* `experiments/projective-cellular-p61-summary.json`;
* `experiments/projective-cellular-p61-harmonic.tsv`;
* `experiments/projective-cellular-p61-qsharp-lifts.tsv`;
* `experiments/projective-cellular-p61-cvp-basis0.json` and its TSV;
* `experiments/projective-cellular-p61-cvp-basis1.json` and its TSV;
* `experiments/projective-cellular-p61-section.json`.

The lift hashes in the section certificate agree with the two TSV SHA-256
hashes.  An independent rational-arithmetic check reproduces `(P61-6)`,
`(P61-9)`, and the exact generalized characteristic polynomial.  The two
JSON lift certificates also contain exact mod-two coset-leader lower bounds
`5` and `6`.

As at level `53`, this is the free lattice of the rational signed
coinvariants, equipped with the compact orbit-coordinate metric.  The
orientation `C_2` coordinates are omitted and the comparison to the free
HAP carry metric remains necessary.  The first of those primary interfaces
is now split uniformly with norm one by
`TRUE_SL3_PRIMARY_TRANSFER_SPLITTING.md`; the residual degree-`(3,2)`
primary block is still open.

## Consequence for the open problem

This result does not prove that every hyperlinear group is sofic.  It does
rule out two simple failure narratives for the selected TRUE charts:

1. the first huge cyclic discriminant was not an isolated chart whose next
   occurrence forces a tiny dual systole; and
2. enormous discriminant order does not force enormous integral repair
   cost at either of the first two cuspidal levels.

The theorem-shaped target is now a family bound on compact harmonic section
norms, followed by the residual primary transfer and the already-isolated
universal chart-selection quantifier.
