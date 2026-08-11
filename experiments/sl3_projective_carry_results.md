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
`docs/TRUE_PROJECTIVE_STABILIZER_HOMOLOGY_BOUNDARY.md`.

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

## Mathematical interpretation

For `p=3,5,7`, Proposition 12 of
`docs/INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` rules out denominator collapse
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
4. lift the concentrated `p=53` harmonic plane to its exact rank-two
   integral lattice and compute its regulator and dual systole.
