# The projective cellular two-primary correction is derived, not coordinatewise

Date: 2026-08-11

## Outcome

The compact signed-coinvariant model used at level `53` has a substantial
two-primary sector.  As an abelian group, its degree-wise zero-th
coinvariants are

`C_0=Z^141`,
`C_1=Z^364 directSum (Z/2)^29`,
`C_2=Z^328 directSum (Z/2)^84`,
`C_3=Z^112 directSum (Z/2)^29`.                         `(TPC1)`

Thus the rational calculation really does discard `84` degree-two torsion
coordinates.  Their number grows with the projective level; they are not a
fixed finite-rank correction.

There is also a decisive structural warning.  If one merely forgets all
orientation signs modulo two, the resulting unsigned orbit complex at
`p=53` has dimensions

`F_2^141 <- F_2^393 <- F_2^412 <- F_2^141`,             `(TPC2)`

boundary ranks `140,253,135`, and homology dimensions

`(1,0,24,6)`.                                          `(TPC3)`

The rational signed complex has homology dimensions `(1,0,2,10)`.  In
particular, the unsigned shadow has mod-two `H_3` dimension `6`, strictly
smaller than the rational `H_3` dimension `10`.  No complex of free
finitely generated abelian groups can have this behavior under reduction
modulo two: universal coefficients force mod-two homology dimension to be at
least the rational Betti number.

Therefore the unsigned orbit complex is **not** the missing free integral
model.  The correct bounded-primary bridge must include the derived homology
of the finite cell stabilizers.  Simply restoring the deleted coordinates is
mathematically insufficient.

This does not alter the exact free-lattice section

`7.489055360091924...<=kappa_Sigma<=7.49017741972933...` `(TPC4)`

proved in `TRUE_P53_CELLULAR_HARMONIC_DISCRIMINANT.md`.  It precisely locates
what remains before `(TPC4)` can be transported to the free HAP carry model.

## Signed orbit coinvariants

For one cell orbit, let a finite stabilizer permute the coefficient points
and multiply the cellular orientation by signs.  On each unsigned point
orbit, choose one generator `e`.  Transport around a stabilizer loop either
returns `e` or returns `-e`.

* If every loop returns `e`, that orbit contributes `Z`.
* If some loop returns `-e`, the relation is `e=-e`, so the orbit contributes
  `Z/2`.

This proves the decomposition in `(TPC1)` directly from the stabilizer
actions exported by `sl3_projective_cellular_export.g`.  Rationally the
second kind vanishes, which is exactly what the existing signed DSU code
does.  Modulo two the sign disappears, so both kinds contribute one
coordinate and give `(TPC2)`.

The new verifier `experiments/sl3_projective_cellular_two_primary.py`
constructs this unsigned complex, checks both products of consecutive
boundaries are zero, and computes every rank over `F_2` exactly.

## Exact finite audit

The following table records the tested projective primes.  The column
`t=(t_1,t_2,t_3)` is the number of orientation-torsion `Z/2` coordinates in
positive degrees.  The last column is the homology dimension vector of the
unsigned mod-two orbit complex.

| `p` | projective degree | rational free dimensions | `t` | unsigned `H_*(F_2)` |
| ---: | ---: | --- | --- | --- |
| 3 | 13 | `(3,2,0,0)` | `(3,8,3)` | `(1,0,3,1)` |
| 5 | 31 | `(5,4,0,0)` | `(5,12,5)` | `(1,0,4,2)` |
| 7 | 57 | `(7,8,4,2)` | `(5,14,5)` | `(1,0,5,1)` |
| 11 | 133 | `(11,18,10,4)` | `(7,20,7)` | `(1,0,6,2)` |
| 13 | 183 | `(15,24,16,6)` | `(9,24,9)` | `(1,0,8,2)` |
| 17 | 307 | `(21,40,28,10)` | `(11,30,11)` | `(1,1,10,3)` |
| 19 | 381 | `(25,50,38,14)` | `(11,32,11)` | `(1,0,10,2)` |
| 23 | 553 | `(33,72,56,20)` | `(13,38,13)` | `(1,0,11,3)` |
| 29 | 871 | `(49,112,92,32)` | `(17,48,17)` | `(1,0,14,4)` |
| 31 | 993 | `(55,128,108,38)` | `(17,50,17)` | `(1,0,15,3)` |
| 53 | 2863 | `(141,364,328,112)` | `(29,84,29)` | `(1,0,24,6)` |
| 61 | 3783 | `(183,480,440,150)` | `(33,96,33)` | `(1,0,28,6)` |

Across these eleven exact cases the torsion-coordinate counts obey the
quasipolynomial pattern

`t_1=t_3=(p+4+chi_(-1)(p))/2`,
`t_2=(3p+8+chi_(-1)(p))/2`,                            `(TPC5)`

where `chi_(-1)(p)=1` for `p=1 mod 4` and `-1` for `p=3 mod 4`.
The residual theorem in
`TRUE_PROJECTIVE_PRIMARY_RESIDUAL_MATCHING.md` now proves, for every odd
prime, the degree-three formula in `(TPC5)` and the `p+2` contribution of the
second degree-two cell.  The equality with the degree-one and first
degree-two counts is still recorded here from the exact finite audit rather
than promoted without its own orbit proof.

One part of the zero-th row is now understood uniformly, without assuming
`(TPC5)`.  The first degree-two stabilizer is `S_4`, the degree-one
stabilizer is an index-three `D_8`, and the cellular transfer is a
permutation isomorphism on their signed `C_2` orbit summands for every finite
coefficient action.  Thus `t_1` of the first degree-two torsion coordinates
cancel against all `t_1` degree-one coordinates with norm-one inverse.  The
exact all-subgroup proof is
`TRUE_SL3_PRIMARY_TRANSFER_SPLITTING.md`.  This cancellation occurs in the
zero-th row only and does not remove the positive derived rows in `(TPC6)`.

The hash-bearing raw result is
`experiments/projective-cellular-two-primary.json`.

## Why the correction is derived

The non-free cellular complex is a resolution over characteristic zero
because the finite stabilizer orders can be inverted.  Integrally, taking
ordinary stabilizer coinvariants is not exact.  The correct object is the
equivariant hyperhomology total complex, or equivalently the spectral
sequence with rows

`H_j(Stab(sigma), orientation_sigma tensor M)`.         `(TPC6)`

The unsigned mod-two orbit complex is only the `j=0` shadow of this object.
The missing higher rows are forced by the contradiction between `(TPC3)`
and the rational Betti number.  They are not optional bookkeeping.

There is nevertheless a reason the phrase *bounded-primary correction*
remains plausible.  Only finitely many cell stabilizer types occur in the
fixed `SL_3(Z)` cellular model; their orders are at most `24`.  Positive
stabilizer homology is killed by the stabilizer order.  Hence all additional
two-primary groups have exponent bounded by `8`, independently of `p`, even
though their ranks grow.  What is not yet proved is a uniformly bounded
Euclidean decoder through the resulting total complex.

## Next exact task

The proposed total-complex construction is already implemented by HAP.
`FreeGResolution(ContractibleGcomplex("SL(3,Z)"),3)` is the Wall
perturbation total complex of the fixed stabilizer resolutions, and
`ResolutionArithmeticGroup("SL(3,Z)",3)` calls it directly.  Thus the large
free projective Shapiro complex already used in this repo is precisely the
required derived integral model.  Its bidegrees, stabilizer types, and
chart-independent Schur bounds are audited in
`TRUE_HAP_DERIVED_TOTAL_AUDIT.md`.

The decisive computation is then to transport the two certified level-53
harmonic lifts through the canonical filtered augmentation into that
already-exported derived free complex and measure the resulting section
norm.  Success gives the missing bounded-primary bridge at this level;
failure identifies an explicit positive stabilizer-homology class
responsible for the obstruction.  Either outcome is more informative than
further work in the naive unsigned orbit complex.
