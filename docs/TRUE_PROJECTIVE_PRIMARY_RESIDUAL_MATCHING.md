# The residual projective orientation-primary boundary is a local matching

Date: 2026-08-11

## Outcome

After cancelling the first degree-two orientation-torsion block against the
degree-one block, the remaining zero-th-row primary boundary on every tested
projective chart has an unexpectedly rigid form.  The map

`T_3 -> T_(2,second)`

over `F_2` is a disjoint union of two-point repetition maps

`x -> (x,x)`,

together with zero source and target coordinates.  Equivalently, every
nonzero matrix row has weight two and every used column has weight one.

This gives a decoder on the image with norm at most one by selecting either
copy (and Moore--Penrose norm `1/sqrt(2)` in the Euclidean realization).
Thus the residual boundary image itself cannot hide a growing-distance
binary code.

The full raw-export computation was performed on twelve primes.  An
independent direct verifier in HAP's natural three-dimensional model checks
the same law for all `42` odd primes at most `191`.  This is still not a
theorem for every odd prime.  It also does not remove the positive
stabilizer-resolution rows in HAP's derived total complex.  The growing
kernel and cokernel coordinates are genuine primary homology and may still
couple to those rows or to the free harmonic lattice.

## Exact family pattern

For all

`p=3,5,7,11,13,17,19,23,29,31,53,61`,

put `chi=(-1|p)`.  The observed dimensions and incidences are

`dim T_3=(p+4+chi)/2`,

`dim T_(2,second)=p+2`,

`rank=(p+1)/2`,

`dim ker=(3+chi)/2`,

`dim coker=(p+3)/2`.                                      `(PRM1)`

More precisely, the row and column histograms are

`rows: 0^((3+chi)/2), 2^((p+1)/2)`,

`columns: 0^1, 1^(p+1)`.                                  `(PRM2)`

Since no target column occurs in two nonzero rows, `(PRM2)` proves that the
nonzero part is permutation-equivalent to `(p+1)/2` copies of `[1 1]`.
There is no numerical conditioning inference here: the block form follows
exactly from the certified sparse matrix.

| `p` | source | target | rank | kernel | cokernel |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 3 | 5 | 2 | 1 | 3 |
| 5 | 5 | 7 | 3 | 2 | 4 |
| 7 | 5 | 9 | 4 | 1 | 5 |
| 11 | 7 | 13 | 6 | 1 | 7 |
| 13 | 9 | 15 | 7 | 2 | 8 |
| 17 | 11 | 19 | 9 | 2 | 10 |
| 19 | 11 | 21 | 10 | 1 | 11 |
| 23 | 13 | 25 | 12 | 1 | 13 |
| 29 | 17 | 31 | 15 | 2 | 16 |
| 31 | 17 | 33 | 16 | 1 | 17 |
| 53 | 29 | 55 | 27 | 2 | 28 |
| 61 | 33 | 63 | 31 | 2 | 32 |

## The generic stratum is symbolic

The natural model makes a proof decomposition visible.  Its degree-three
stabilizer is `S_4` in a three-dimensional rational representation.  The
orientation-reversing elements have six rational projective fixed planes,
the reflection mirrors.  Parameterize any one of them by

`v(t)=v_0+t v_1` over `Q(t)`.

The exact rational-function verifier enumerates the six residual boundary
matrices and all twelve target-stabilizer matrices.  On **each** of the six
mirrors it proves:

1. exactly two boundary images are generically target-nonorientable;
2. those two images lie in distinct target-stabilizer orbits; and
3. each occurs with multiplicity one.

Thus the generic residual row is exactly `[1 1]`; this is no longer merely
a finite-prime pattern.  Every possible failure is confined to finitely many
parameters.  On each mirror the verifier computes seven rational linear
exception factors, plus the point at infinity.  Across the six chosen
coordinates the factors are drawn from

`t, t+1/2, t+1, t+1/3, t+2, t+3, t-1, t-1/2,`
`t-1/3, t-1/4, t-2, t-2/3, t-3, t-3/4, t-3/2,`
`t-4/3, t-4`.

This leaves a finite exceptional-orbit calculation and the nonrational
4-cycle eigenlines.  The latter explain why the observed kernel count
depends on `chi=(-1|p)`: the `+-i` projective eigenlines exist over `F_p`
exactly when `-1` is a square.  That explanation is currently a derived
conjecture from the representation type; the exceptional strata still need
an explicit all-prime proof.

The symbolic program is `experiments/sl3_projective_primary_generic.py`,
fed by the exact HAP template exporter
`experiments/sl3_projective_primary_template_export.g`.  Its compact output
is `experiments/sl3-primary-generic-summary.tsv`, with SHA-256
`07da64831418c5ea0814ea20faf37246ef257b3b49c6463426f1cec6d150ac90`.

## Construction checked

The compact degree-three boundary has six terms landing in the second
degree-two cell.  For each nonorientable degree-three orbit, the verifier
chooses one representative, applies those six fixed permutations, reduces
the images to nonorientable target orbits, and sums modulo two.  It then
computes the exact sparse rank and complete row/column weight histograms.

The program is `experiments/sl3_projective_primary_residual.py`; the compact
machine-readable table is `experiments/projective-primary-residual.tsv`,
with SHA-256
`6c6a48b0d8c64f0ac212b027cc0e03268f589c788cee69a585a3f0f456967118`.
The independent natural-model verifier is
`experiments/sl3_projective_primary_natural_audit.g`.  It acts directly on
`P^2(F_p)` using the fixed `3 x 3` stabilizer and boundary matrices from
`ContractibleGcomplex("SL(3,Z)a")`; its verified-prime manifest is
`experiments/projective-primary-natural-audit.txt`, with SHA-256
`a101cc89013657c2f4577e5d7379b1684e1ddd89d3dacaab8d8bf6c5dad88763`.
The raw cellular inputs and all arithmetic were generated on MSI.  No dense
matrix optimization was used.

## Consequence and next proof target

Together with the uniform norm-one cancellation of the first primary
interface, this rules out a high-covering-radius code in the image of either
zero-th-row orientation-primary boundary on every tested chart.  The
remaining zero-th-row primary coordinates split into explicit local
homology:

* `(3+chi)/2` unused degree-three coordinates;
* one unused second-degree coordinate; and
* one cokernel coordinate for each repetition pair.

The immediate theorem-synthesis task is to prove `(PRM1)--(PRM2)` for all
odd primes from the fixed stabilizer actions on the projective plane.  The
more important derived task is then to trace these local homology
coordinates through the positive stabilizer-resolution rows of
`FreeGResolution`.  If those couplings also split by fixed local templates,
the feared orientation-primary decoder obstruction disappears for the
selected projective family.
