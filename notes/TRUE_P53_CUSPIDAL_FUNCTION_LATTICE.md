# A compact exact integral model of the level-53 cuspidal plane

Date: 2026-08-11

## Outcome

The projective Shapiro complex at level `53` has a two-dimensional harmonic
sector, but a normalized rational basis in its `28,630` degree-two cell
coordinates has large height.  Three exact modular lifts were not enough for
stable rational reconstruction.

There is a much smaller integral presentation of the same rational cuspidal
cohomology.  The Ash--Grayson--Green model describes it as a space of
functions

`f:P^2(F_p)->Q`                                                     `(CFL1)`

satisfying signed symmetry, a three-term modular-symbol relation, vanishing
on one boundary line, and a parabolic sum relation.  At `p=53`, exact
computation reduces all `2,863` function coordinates to `100` signed-symmetry
orbits.  The remaining `204` distinct integer relations have rank `98`.
Therefore their exact integral kernel has rank two.

An LLL-reduced integral basis has maximum coefficient `12`, support sizes

`1,824` and `1,896`,                                               `(CFL2)`

and Gram matrix

`G_53=[[7872,-3264],[-3264,71424]].`                               `(CFL3)`

Its determinant is

`det(G_53)=551596032=2^12*3^2*13*1151.`                            `(CFL4)`

The complete basis is stored in
`experiments/projective-cuspidal-p53-basis.tsv`.  The generating script
independently evaluates every basis vector in all six displayed relation
families; every exact residual is zero.  The hash-bearing summary is
`experiments/projective-cuspidal-p53-summary.json`.

This is a real exact arithmetic reduction, but it does **not** yet prove a
uniform integral carry decoder.  The Euclidean metric in the HAP degree-two
cell complex is not automatically the function-coordinate metric `(CFL3)`.
The missing finite object is an explicit integral comparison map between this
cuspidal function lattice and the harmonic lift sequence

`0 -> L -> M_Sigma -> Q^# -> 0`                                   `(CFL5)`

from `TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md`.

## The four function relations

Write projective points as homogeneous triples `(x:y:z)`.  The model uses:

`f(x,y,z)=f(z,x,y)=f(-x,y,z)=-f(y,x,z)`,                           `(CFL6)`

`f(x,y,z)+f(-y,x-y,z)+f(y-x,-x,z)=0`,                             `(CFL7)`

`f(x,y,0)=0`,                                                     `(CFL8)`

and, for `(x,y)!=(0,0)`,

`sum_(z in F_p) f(x,y,z)=0`.                                      `(CFL9)`

These are the relations quoted in Theorem A.16 of the computational appendix
to *Explicitly Computing Modular Forms* and in Gunnells' modular-symbol
lectures.  The implementation first imposes `(CFL6)` and `(CFL8)` with a
signed disjoint-set quotient.  It then constructs `(CFL7)` and `(CFL9)` over
the quotient, removes duplicate primitive rows, computes the saturated
integer right kernel, and lifts it back to all projective coordinates.

The signed quotient is the decisive speedup:

`2863 coordinates -> 100 signed variables -> rank-2 kernel.`       `(CFL10)`

No large sparse elimination or modular reconstruction is needed.

## Calibration

The same exact implementation gives the known low-level pattern:

| prime level | projective points | signed variables | cusp dimension |
| ---: | ---: | ---: | ---: |
| `3` | `13` | `0` | `0` |
| `5` | `31` | `0` | `0` |
| `7` | `57` | `1` | `0` |
| `53` | `2,863` | `100` | `2` |
| `61` | `3,783` | `136` | `2` |

At level `61`, the integral basis again has maximum coefficient `12` and
Gram matrix

`[[25776,-4752],[-4752,44064]].`                                  `(CFL11)`

The zero dimensions at `3,5,7` agree with the acyclic Shapiro calculations;
the two-dimensional results at `53,61` agree with the published list of the
first prime levels carrying cusp forms.  This is an independent structural
calibration of the relation implementation.

## Relation to the modular HAP basis

`experiments/sl3_projective_carry_results.md` now contains exact HAP harmonic
bases over `F_101`, `F_1009`, and `F_10007`.  Thus both sides of the desired
comparison are finite and exact:

`rank-2 integral AGG function lattice`

`<---- explicit chain/duality comparison ---->`

`rank-2 HAP harmonic plane modulo three primes.`                   `(CFL12)`

The next computation should construct `(CFL12)`, not accumulate anonymous CRT
primes.  A comparison modulo one prime is enough to identify the two basis
directions.  Once the comparison is written as an integral cellular map, the
small basis `(CFL2)--(CFL4)` can be transported into the harmonic lift problem,
where two affine integer lifts give the complete decoder bound.

There are two plausible implementations:

1. realize the function model as the top-cell cocycles on the well-rounded
   retract and compute a chain map to the fixed HAP resolution;
2. use the explicit modular-symbol representatives in the AGG construction,
   reduce them through the HAP contracting homotopy, and pair them with the
   three verified modular harmonic bases.

Either route is a fixed finite comparison at level `53`.  The important new
fact is that the arithmetic cusp lattice itself is no longer hidden inside a
`28,628`-dimensional rational solve.

`TRUE_CHAIN_COMPARISON_DECODER_TRANSFER.md` gives the exact payoff for this
comparison.  Integral cochain maps in both directions which induce inverse
maps on the rank-two cuspidal lattice transport every integral lift section;
the decoder norm grows by at most the product of the two degree-two map
norms.  Consequently the comparison does not need to output a rational HAP
harmonic basis.  It may transport two compact-model integral lifts directly
and certify the resulting HAP decoder through the chain identities.

The family-level norm of a fixed comparison is not an additional unknown.
`TRUE_FIXED_RESOLUTION_DECODER_INVARIANCE.md` proves that fixed group-ring
comparison matrices specialize with uniformly bounded normalized `L2`
norms on every projective set.  For the well-rounded/modular-symbol cellular
model this is automatic after inverting the finite cell-stabilizer orders.
Thus the live comparison issue is the bounded-primary integral correction,
especially the observed two-primary sector, rather than growth of the real
chain-map norm with `p`.

## Status for the open problem

The exact integral function lattice solves a genuine finite arithmetic
subproblem and supplies a compact certificate for the first cuspidal chart.
It does not settle hyperlinear versus sofic.  To advance the TRUE route, one
must still transport its lattice and norm into `(CFL5)` and then prove a
uniform decoder statement across a selected asymptotically free chart family.
The computation changes the next step from high-height rational recovery to a
small explicit chain-map problem.
