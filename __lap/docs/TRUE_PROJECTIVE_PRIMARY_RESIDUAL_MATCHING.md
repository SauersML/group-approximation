# The residual projective orientation-primary boundary is a local matching

Date: 2026-08-11

## Outcome

After cancelling the first degree-two orientation-torsion block against the
degree-one block, the remaining zero-th-row primary boundary on every odd
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

The result is now a theorem for every odd prime.  Its proof is a projective
orbit calculation for two fixed finite matrix groups: the source torsion
orbits are one copy of `P^1(F_p)` modulo

`phi(t)=t/(2t-1)`,

plus a possible order-four eigenline, while the target torsion orbits are two
copies of the same quotient glued at one point.  The residual boundary sends
each source parameter to the corresponding point in both target copies.

This does not remove the positive stabilizer-resolution rows in HAP's
derived total complex.  The growing kernel and cokernel coordinates are
genuine primary homology and may still couple to those rows or to the free
harmonic lattice.

## Exact family pattern

Let `p` be any odd prime and put `chi=(-1|p)`.  The dimensions and
incidences are

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

## Uniform projective-orbit proof

Work over `k=F_p`, with row vectors.  In HAP's natural three-dimensional
model let `K` be the degree-three stabilizer and `J` the second degree-two
stabilizer, with their cellular orientation characters.  Direct
multiplication of the fixed integral matrices gives

`K ~= S_4`, with six negative involutions and six negative elements of order
`4`, and

`J ~= D_12`, with six negative involutions in two conjugacy classes.

The reductions retain orders `24` and `12` for every odd `p`.  Choose

```text
r = [[ 1, 1, 1],       z = [[-1, 0, 0],
     [ 0,-1, 0],            [ 0, 1, 0],
     [ 0, 0,-1]]            [ 0,-2,-1]],

w = [[ 0, 1, 0],       D = [[ 1, 0, 0],
     [-1, 0, 0],            [ 0,-1, 0],
     [ 2, 0, 1]]            [-2, 0,-1]].
```

Here `r` is negative and belongs to both groups, `z` is positive and belongs
to both groups, `w` is a negative order-four element of `K`, and `D` is the
last residual boundary matrix.

### Source orbits

The `(-1)`-eigenplane of `r` is

`E={ [0:y:z] } ~= P^1(k)`.

Write `v(t)=[0:1:t]` and `v(infinity)=[0:0:1]`.  On `E`, the matrix `z`
induces the involution

`phi(t)=t/(2t-1)`, with `phi(infinity)=1/2` and `phi(1/2)=infinity`.

The exact `24`-matrix calculation in `K` has the following concise form.
Every projective line fixed by a negative involution is `K`-equivalent to a
point of `E`, and two points of `E` are `K`-equivalent exactly when their
parameters differ by `phi`.  To see that there are no exceptional extra
identifications, inspect `g(E) intersect E` for the `24` matrices `g`: the
four matrices preserving `E` induce `1` or `phi`; every other nonempty
intersection is one of `t=0`, `t=1/2`, or `t=infinity`, already contained in
a `phi`-orbit.

The involution `phi` has exactly the two fixed points `0` and `1`.  Hence

`|P^1(k)/phi|=(p+3)/2`.                                    `(PRM3)`

The negative order-four elements are one `K`-conjugacy class.  The
characteristic polynomial of `w` is

`(X-1)(X^2+1)`.

Its `1`-eigenline is carried by a fixed `K`-matrix to `v(0)`, so it is
already in `(PRM3)`.  If `chi=-1` there are no further eigenlines over `k`.
If `chi=1`, choose `i^2=-1`; the two lines represented by `(i,1,0)` and
`(-i,1,0)` are interchanged by a fixed element of `K`, and supply exactly one
additional orbit.  Thus the source count is

`(p+3)/2 + (1+chi)/2 = (p+4+chi)/2`.                       `(PRM4)`

### Target orbits

The two negative conjugacy classes in `J` are represented by `r` and `zr`.
Their `(-1)`-eigenplanes are

`E={x=0}` and `F={x=2z}=D(E)`.

Their positive eigenlines already lie in the other negative eigenplane, so
these two planes contain every target nonorientable orbit.  Within either
plane the orbit relation is again `P^1(k)/phi`: on `E` it is induced by `z`,
and on `F` it is its `D`-conjugate.  Multiplication of the twelve matrices in
`J` shows that an orbit from `E` meets an orbit from `F` only at

`u=[0:1:0]=v(0)`.

Consequently the target is two copies of `(PRM3)` glued at `u`, and has

`2 (p+3)/2 - 1 = p+2`                                      `(PRM5)`

nonorientable orbits.

### The boundary matrix

The six residual boundary matrices, in their HAP order, are

`I,B_2,B_3,B_4,w,D`.

For every `v=(0,y,z)` in `E`, direct multiplication gives the projective
identities

`v B_2 = v B_4`, and `v B_3 = v w`.                        `(PRM6)`

The paired terms in `(PRM6)` cancel over `F_2`.  The row indexed by the
source class `[v] in E/phi` is therefore exactly

`[v]_E + [vD]_F`.                                           `(PRM7)`

Both maps in `(PRM7)` are bijections onto their target copies.  For `v=u`
the two coordinates are the common glued coordinate and cancel.  Every
other source class gives two distinct coordinates, and different classes
give disjoint pairs.  Thus the transposition stratum gives one zero row and
`(p+1)/2` disjoint `[1 1]` rows, using every target column except `u`.

It remains only the possible order-four orbit.  For `i^2=-1`, take
`a=(i,1,0)`.  The six images pair in target projective orbits as

`a I ~ a w`, `a B_2 ~ a D`, and `a B_3 ~ a B_4`.

The first equivalence uses `aw=ia`, the second is scalar equality, and for
the third `(aB_3)r` is a scalar multiple of `aB_4`.  Hence this extra row is
zero.  Combining this with `(PRM3)--(PRM7)` proves `(PRM1)--(PRM2)` for every
odd prime.

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
An independent exact `Q(t)` stratification is implemented by
`experiments/sl3_projective_primary_generic.py`, using the templates from
`experiments/sl3_projective_primary_template_export.g`.  It finds `[1,1]`
on all six generic reflection planes, the single rational zero orbit
`[0:1:0]`, and the single nonrational zero orbit
`[1:(1+i)/2:(1+i)/2]`.  Its compact outputs are
`experiments/sl3-primary-generic-summary.tsv` and
`experiments/sl3-primary-exception-summary.tsv`; the latter has SHA-256
`b2f68004f66ffec17c6c3864cdd0c3ce3136f0b66d4dfda9b71de5a459c4c812`.
The raw cellular inputs and all arithmetic were generated on MSI.  No dense
matrix optimization was used.

## Consequence and next proof target

Together with the uniform norm-one cancellation of the first primary
interface, this rules out a high-covering-radius code in the image of either
zero-th-row orientation-primary boundary on every odd projective chart.  The
remaining zero-th-row primary coordinates split into explicit local
homology:

* `(3+chi)/2` unused degree-three coordinates;
* one unused second-degree coordinate; and
* one cokernel coordinate for each repetition pair.

The zero-th-row theorem-synthesis task is complete.  The next derived task
is to trace these local homology coordinates through the positive
stabilizer-resolution rows of
`FreeGResolution`.  If those couplings also split by fixed local templates,
the feared orientation-primary decoder obstruction disappears for the
selected projective family.
