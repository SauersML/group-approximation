# Exact arithmetic on the projective `SL_3(Z)` charts

Date: 2026-08-11

## Outcome

The projective charts on

`Y_p=P^2(F_p)`

remove the scalar-character gluing code from the earlier nonzero-vector
charts.  The first exact computations establish three useful facts.

1. At `p=3`, the integer image of the carry boundary is not saturated: its
   Smith form has one nonunit factor `2`.
2. An exact integral projection onto the saturated real image exists after
   denominator clearing, but the canonical Smith projection has enormous
   norm.  Lattice reduction removes most of this basis artifact, while still
   leaving a large gap to the observed carry ratio.
3. The point stabilizers at `p=3,5,7` have zero rational second homology.
   Their exact integral second homology is small two-torsion.

These are genuine exact subresults.  They do **not** prove that every
hyperlinear group is sofic.  In particular, rational two-acyclicity cannot
hold uniformly over the projective prime family; see
`notes/TRUE_PROJECTIVE_STABILIZER_HOMOLOGY_BOUNDARY.md`.

## Projective `p=3` carry lattice

`sl3_projective_charts.py` constructs the exact trivial-character boundary
on the 13 points of `P^2(F_3)`.  Its dimensions are

`vertices=13, edges=78, cells=169, rank(d1)=66`.

The nonunit Smith factors of `d1` are exactly `[2]`.  Thus the primitive
lattice

`L=ran_R(d1) intersect Z^169`

is larger than `ran_Z(d1)` by one `C_2` direction.  This independently
confirms that projectivizing removes the scalar gluing code but does not
remove arithmetic saturation defects.

`sl3_carry_rational_projection.py` constructs exact matrices `L,R,C,P` and
the denominator `M=2` satisfying

`R L=I`, `P=L R`, `P^2=P`, `P d1=d1`,

`d1 C=2P`, and `d1 C d1=2d1`.

The construction is therefore an exact denominator-cleared splitting.  Its
canonical Smith representative is geometrically useless:

`||I-P||_2 = 45473.56252411015`.

This distinction matters.  Existence of an integral projection does not by
itself give the uniform metric bound required for circle-phase repair.

## Lattice reduction of the exact projection

`sl3_projective_projection_reduce.py` reduces the rows of the exact right
inverse modulo the integer left kernel.  BKZ block size 10 followed by eight
coupled coordinate sweeps gives:

| quantity | Smith representative | nearest-plane | coupled result |
| --- | ---: | ---: | ---: |
| right-inverse row energy | 25,611,332 | 163 | 163 |
| `||I-P||_2` | 45,473.5625 | 190.3719 | 181.7476 |
| `||I-P||_F^2` | 2,067,847,899 | 40,749 | 38,383 |
| maximum coefficient | 6,468 | 20 | 17 |

All exact identities survive reduction.  The reduction proves that almost
all of the Smith explosion was a bad choice of representatives.  It also
shows that independent row CVP plus local Frobenius descent is not yet the
desired decoder: `181.75` is still far above the approximately `4.54`
fixed-axis carry lower bound measured on these charts.

The next optimization should therefore be structural and coupled, rather
than another blind increase of the BKZ block size.

## Stabilizer `H_2` by Shapiro's lemma

Let `H_p` be the stabilizer of a point in the action of `SL_3(Z)` on
`P^2(F_p)`.  Shapiro's lemma identifies

`H_2(H_p,Z) ~= H_2(SL_3(Z), Z[P^2(F_p)]).`

`sl3_projective_h2_export.g` applies the fixed HAP resolution of `SL_3(Z)`
directly to the projective permutation module.  It reduces each coefficient
matrix modulo `p` and acts on rank-one projective lines, avoiding expensive
word decomposition in the infinite group.  The degree-two and degree-three
resolution boundaries contain only 83 and 597 coefficient terms,
respectively.

`sl3_projective_h2_analyze.py` checks `d3*d2=0`, computes exact rational and
modular ranks, and asks Sage's integer chain-complex code for the full
finitely generated abelian group.  The exact results are:

| `p` | `n=p^2+p+1` | `rank_Q(d2)` | `rank_Q(d3)` | `dim_Q H_2` | `H_2(H_p,Z)` |
| ---: | ---: | ---: | ---: | ---: | --- |
| 3 | 13 | 40 | 90 | 0 | `C_2^3` |
| 5 | 31 | 94 | 216 | 0 | `C_2^3` |
| 7 | 57 | 172 | 398 | 0 | `C_2^4` |

The rational ranks obey the small-level pattern

`rank_Q(d2)=3n+1`, `rank_Q(d3)=7n-1`,

so the middle dimension `10n` is exhausted.  This is a useful exact pattern
to explain from the fixed resolution and the permutation character, but it
must **not** be extrapolated to all primes: cuspidal cohomology forces
nonzero rational `H_2` at later prime levels.

The modular dimensions are:

| `p` | `dim H_2(F_2)` | `dim H_2(F_3)` | `dim H_2(F_5)` | `dim H_2(F_7)` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 4 | 0 | 0 | 0 |
| 5 | 4 | 0 | 0 | 0 |
| 7 | 5 | 1 | 0 | 0 |

At `p=7`, the integral result has no three-torsion in `H_2`; the extra
mod-three class is therefore a universal-coefficient contribution from
`H_1`, not hidden three-torsion in `H_2`.

The raw sparse boundaries and analyzer summaries are committed as
`projective-h2-p{3,5,7}-direct-{d2,d3}.tsv` and
`projective-h2-p{3,5,7}-direct.json`.  The summaries contain SHA-256 hashes
of the exact boundary files.

## First cuspidal level: exact `p=53` rank

The first literature-certified projective level with nonzero cuspidal
cohomology is `p=53`, where `n=2863`.  The Shapiro complex has dimensions

`11452 -> 28630 -> 57260`

in degrees one, two, and three.  Its two sparse boundaries have 232,070 and
1,603,070 nonzero entries.  Exact ranks are:

| field | `rank(d2)` | `rank(d3)` | `dim H_2` |
| --- | ---: | ---: | ---: |
| `F_2` | 8,589 | 20,029 | 12 |
| `F_3` | 8,590 | 20,038 | 2 |
| `F_5` | 8,590 | 20,038 | 2 |
| `F_7` | 8,590 | 20,038 | 2 |
| `F_101` | 8,590 | 20,038 | 2 |

Ash--Yasaki compute that the cuspidal degree-three cohomology at level 53
has dimension two.  Poincare--Lefschetz duality therefore gives
`dim_Q H_2>=2`, while reduction modulo 101 gives `dim_Q H_2<=2`.  Hence

`dim_Q H_2(H_53,Q)=2`.

This is the first exact computation in the selected chart family where the
harmonic carry sector is genuinely present.  The jump to dimension 12 in
characteristic two also shows that substantial two-primary homology or a
universal-coefficient contribution survives beyond the free rank.

The optimized exporter replaces two quadratic operations by a projective
point dictionary and a direct inverse-permutation lookup.  At `p=3` it is
byte-for-byte identical to the original exporter.  At `p=53` it writes the
full complex in 13.43 seconds using about 167 MiB, so export is no longer a
bottleneck.  The boundary hashes and exact ranks are in
`projective-h2-p53-summary.json`; the 26 MiB reproducible raw text matrices
are intentionally not stored in Git.

## Numerical metric probe at `p=53`

`sl3_projective_harmonic_probe.py` applies

`Delta_2=d2 d2^T+d3^T d3`

as a sparse linear operator, without materializing the Laplacian.  A
diagonally preconditioned six-vector LOBPCG run found eigenvalues

`2.42e-16, 2.11e-13, 0.193773, 0.306577, 0.383428, 0.417535`.

The first two vectors independently satisfy the cycle and boundary
orthogonality equations to at worst `3.55e-7`; the next eigenvalue is
separated by `0.19377`.  Thus the numerical Hodge kernel cleanly reproduces
the exact harmonic dimension two.

The harmonic leverage is highly nonuniform among the ten degree-two cell
orbits.  Their leverage sums are approximately

`0.0143, 0.0224, 0.0174, 0.0410, 0.0713,`
`0.0493, 0.0884, 1.2830, 0.2484, 0.1645`.

The eighth orbit alone carries 64.15 percent of the two-dimensional plane.
In the fixed HAP resolution this is the five-term cell with boundary

`[[-1,23],[2,23],[2,27],[-4,30],[4,32]]`.

This concentration is the first concrete reduction for the harmonic
systole calculation: eliminate the other nine cell orbits by a sparse
Schur complement and lift the resulting two coordinates exactly.  The full
numerical certificate is in `projective-h2-p53-harmonic.json`.

Generic Sage sparse-kernel extraction was also tested with both echelon and
raw computed bases.  Each remained compute-bound at the five-minute cap;
the live exact-basis implementation should use pivot-guided sparse solving
or a purpose-built block-Wiedemann routine, not a larger generic echelon
job.

## Pivot-guided `p=53` exact-recovery benchmark

The nonlinear discriminant formula in
`notes/TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` makes an exact rational
basis of the harmonic two-plane the next input.  A second bounded MSI audit
localized the computational obstruction more precisely.

Rerunning LOBPCG with four vectors selected the well-conditioned free
coordinates

`22551, 21965`.

Their harmonic residuals in the two defining equations were at most
`1.97e-10`.  Over `F_101`, exact sparse row-profile extraction then selected

`8,590` independent rows of `d2^T`,
`20,038` independent rows of `d3`.

This took `47.06` seconds in total and used at most about `1.14` GiB.
Deleting the two numerical free columns reduces the full 68,712-row stack
to one square candidate system of order `28,628`.  Direct integer
aggregation found only `477,925` distinct positions before modular zero
removal, and a native LinBox implementation assembled the matrix and
right-hand side in `0.589` seconds.

The remaining cost is entirely elimination fill:

| exact operation | cap | outcome |
| --- | ---: | --- |
| Sage sparse square solve, two right-hand sides | 300 s | timed out |
| native LinBox sparse elimination, one right-hand side | 180 s | timed out |
| Sage/LinBox rank of the reduced square matrix | 90 s | timed out |

Every process from this benchmark ended at its cap and none remains.  The
benchmark summary is stored in `projective-h2-p53-pivot-benchmark.json`, and
`sl3_projective_harmonic_modular.py` reproduces the exact row profiles and
supports the pivot-guided solve when a suitable backend is available.

This rules out another blind increase in generic exact-elimination time.
The next implementation should either:

1. apply a genuine block-Wiedemann/nullspace solver to the reduced sparse
   system; or
2. exploit the ten HAP cell blocks and eliminate the nine low-leverage
   blocks symbolically before exact arithmetic.

The second option is especially attractive because 64.15 percent of the
harmonic leverage is already concentrated in block eight.  A successful
Schur complement would turn the exact recovery into a structured lift from
that block rather than an unstructured order-28,628 elimination.

## Exact modular harmonic bases with SpaSM

A specialized sparse finite-field backend removes the elimination bottleneck.
SpaSM revision `09c4094` was built against the existing Sage finite-field
libraries.  Its default block size repeated an expensive triangular update,
but setting the dense block size to `14,000` processes the residual core in
one FFLAS-FFPACK call.  With four threads, the same pivot-guided square system
is solved in under 46 seconds at each of three primes:

| field | sparse pivots | dense core | full rank | echelonization |
| --- | ---: | ---: | ---: | ---: |
| `F_101` | 15,170 | 13,458 | 28,628 | 29.683 s |
| `F_1009` | 15,221 | 13,407 | 28,628 | 40.227 s |
| `F_10007` | 15,220 | 13,408 | 28,628 | 45.601 s |

The exporter combines duplicate cellular entries before writing the exact
SpaSM systems.  Each square matrix has `474,612` nonzero entries and each
two-row right-hand side has `24`.  The verifier reconstructs the two full
`28,630`-coordinate vectors and checks all original `d2^T` and `d3`
equations.  Every residual is exactly zero at all three primes.  Hashes and
timings are stored in `projective-h2-p53-spasm.json`; the large raw solutions
remain on shared compute storage.

This is an exact modular basis of the harmonic plane, but not yet a rational
or integral basis.  The normalized coordinates are not small integers:
only `66` of `57,260` centered entries agree between characteristics `101`
and `1009`.  Standard rational reconstruction from modulus `101*1009`
returns candidates at `34,356` coordinates, while reconstruction after
adding characteristic `10007` returns `34,424`; only six earlier candidates
remain unchanged.  Thus the two-prime candidates were almost entirely
reconstruction noise, and the rational height is already beyond this
three-prime modulus on nearly every nontrivial coordinate.

The computational conclusion is sharp.  Exact prime-field recovery is now a
fast primitive, so further primes are feasible, but a blind CRT sweep is not
yet justified.  The next step should use these modular bases to recover an
arithmetic invariant that needs only residues--for example determinant or
Smith-index data--or derive a height bound before launching rational
reconstruction.  Generic sparse elimination is no longer the bottleneck.

The first such change of coordinates is now exact.  The
Ash--Grayson--Green cuspidal function model reduces the same level-53 rational
cuspidal sector from `2,863` projective coordinates to `100` signed variables
and a rank-two integral kernel with coefficients bounded by `12`.  Its basis
Gram matrix is `[[7872,-3264],[-3264,71424]]`.  This does not yet transport
the HAP Euclidean metric, but it replaces blind CRT by a finite chain-map
comparison between two certified rank-two models.  See
`notes/TRUE_P53_CUSPIDAL_FUNCTION_LATTICE.md`.

## Mathematical interpretation

### Compact cellular harmonic discriminant at `p=53`

The non-free HAP complex `ContractibleGcomplex("SL(3,Z)")` produces a much
smaller rational projective complex

`Q^141 <- Q^364 <- Q^328 <- Q^112`

with boundary ranks `140,224,102` and `H_2` dimension two.  Exact lattice
arithmetic in its free signed-coinvariant coordinates gives

`Q^#/(K intersect H) ~= Z/qZ`,

where

`q=17269229743444936295695902979877937666574454551881432366677092780148396252626561139`.

The shortest nonintegral dual vector has squared norm `a/q` with

`a=1231626080044198340111057047829063373386905262559674403703730158374753002756468263`,

hence norm `0.2670563781...`.  Since `12a<q`, it is below the spherical
threshold.  Saturated-range BKZ/Babai reduction finds the exact four-term
integral lift

`e_240-e_287-e_302+e_304`.

An exhaustive check of `656` signed singletons and `214,512` signed pairs
rules out every lift of squared norm below four.  Therefore this class has
exact lift energy `4` and exact paired distortion
`2sqrt(q/a)=7.4890553601...`.  The original HNF lift's huge norm was only a
basis artifact.  The certificate is `projective-cellular-p53-cvp-exact.json`.

The second Gauss-reduced basis vector has a verified sixteen-term integral
lift of squared norm `16`.  Its support is disjoint from the exact four-term
lift, so the rank-two lift Gram matrix is exactly `diag(4,16)`.  Against the
exact reduced harmonic Gram matrix, the generalized squared singular values
are

`20.236460080505854...`, `56.10275777902312...`.

Hence the full integral section has norm `7.49017741972933...`, while the
first class forces `kappa_Sigma>=7.489055360091924...`.  The compact free
harmonic decoder at `p=53` is therefore bounded within a relative interval
of about `1.5*10^(-4)`.  The exact polynomial is in
`projective-cellular-p53-section.json`; the second lift is in
`projective-cellular-p53-cvp-basis1-certified.tsv`.

This is a certificate for the compact free coinvariant lattice.  It omits
two-primary orientation-torsion coordinates and uses a different Euclidean
metric from the free HAP carry complex, so a bounded integral chain
comparison is still required.  Full details and scope are in
`notes/TRUE_P53_CELLULAR_HARMONIC_DISCRIMINANT.md`; the machine certificate is
`projective-cellular-p53-summary.json`.

### Replication at the second cuspidal level `p=61`

The same compact calculation at `p=61` gives dimensions

`183 <- 480 <- 440 <- 150`,

boundary ranks `182,298,140`, and exact degree-two homology dimension two.
The harmonic discriminant is cyclic of order

`784027680124070571244902013018900874324624829344998811622894236133560467890375653648339615390452725402770059419298`.

Its shortest nonintegral dual vector has norm `0.3532226522900641...`, so
it is farther from zero than the level-`53` vector and is above the
level-`61` spherical threshold `1/sqrt(28)`.  Exact lattice reduction finds
two integral lifts with Gram matrix

`[[17,-3],[-3,10]]`.

The generalized squared singular values are
`22.239342479055036...` and `139.0902358480397...`, giving a certified full
section norm `11.793652354043665...`.  Exact mod-two coset-leader
optimization gives lift-energy lower bounds `5` and `6`; the first yields
`kappa_Sigma>=6.330477286783821...`.  This is a second modest compact
harmonic decoder, not a proof of uniformity.  The exact artifacts are the
`projective-cellular-p61-*` files, and the mathematical statement is in
`notes/TRUE_P61_CELLULAR_HARMONIC_SECTION.md`.

The zero-th orientation-primary row has also been narrowed exactly.  For
every finite coefficient action, the first degree-two `S_4` torsion block
maps by a permutation isomorphism onto the degree-one `D_8` torsion block.
At levels `53` and `61` this accounts for `29` and `33` norm-one matched
pairs.  The residual zero-row primary issue lies between degree three and
the second degree-two cell; positive stabilizer-homology rows in the derived
HAP complex remain separate.  See
`notes/TRUE_SL3_PRIMARY_TRANSFER_SPLITTING.md`.

That residual zero-row map is now uniform as well.  For every odd prime it
is permutation-equivalent over `F_2` to `(p+1)/2` copies of `[1 1]`, together
with `(3+chi_(-1)(p))/2` zero source coordinates and one zero target
coordinate.  The proof classifies the fixed projective lines of the two
negative conjugacy classes in the `S_4` and `D_12` stabilizers: both target
families are `P^1(F_p)` modulo `t -> t/(2t-1)`, glued at the unique cancelled
coordinate.  Hence neither zero-th-row primary interface can create a
growing-distance code.  The positive stabilizer-resolution rows remain the
derived arithmetic gate.  See
`notes/TRUE_PROJECTIVE_PRIMARY_RESIDUAL_MATCHING.md`.

For `p=3,5,7`, Proposition 12 of
`notes/INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` rules out denominator collapse
through real stabilizer homology: the relevant harmonic space is zero.
Together with bounded spherical templates, every nonzero discriminant class
on these three charts has a positive denominator-radius floor.

That leaves numerator growth as the live metric failure mode on these
charts.  Globally, later primes also require controlling the nonzero
harmonic lattice.  The next high-yield tasks are therefore:

1. explain the small-level rank pattern from the resolution's projective
   permutation character, as a calibration rather than a universal claim;
2. split off bounded spherical templates explicitly;
3. synthesize a coupled integral decoder for the torsion and harmonic
   sectors and measure its norm;
4. transport the explicit `p=53,61` rank-two sections through the derived
   bounded-primary/model-comparison bridge and determine whether their
   compact norms remain uniform at further cuspidal primes.

### Two-primary signed-orbit audit

The compact rational quotient omits a growing orientation-torsion sector.
At `p=53` the zero-th signed coinvariants have `Z/2` coordinate counts
`(0,29,84,29)`, while the unsigned mod-two orbit complex has dimensions
`(141,393,412,141)`, ranks `(140,253,135)`, and homology dimensions
`(1,0,24,6)`.

The last value is smaller than the rational signed `H_3` dimension `10`, so
the unsigned complex cannot be the mod-two reduction of a free integral
model.  The missing comparison must include derived finite-stabilizer
homology.  Exact results for eleven primes are in
`projective-cellular-two-primary.json`; interpretation and the next total
complex construction are in
`notes/TRUE_TWO_PRIMARY_CELLULAR_DERIVED_AUDIT.md`.
