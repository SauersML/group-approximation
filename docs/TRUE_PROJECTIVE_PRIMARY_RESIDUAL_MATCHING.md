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

This is an exact computation on twelve primes, not yet a theorem for every
odd prime.  It also does not remove the positive stabilizer-resolution rows
in HAP's derived total complex.  The growing kernel and cokernel coordinates
are genuine primary homology and may still couple to those rows or to the
free harmonic lattice.

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
