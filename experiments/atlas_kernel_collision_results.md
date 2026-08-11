# Exact collision windows for the binary Leavitt atlas

Date: 2026-08-11

## Purpose

`atlas_kernel_collision_enumerator.py` implements Proposition 4 of
`docs/FALSE_RECURSIVE_ATLAS_EXHAUSTION.md`.  It enumerates the ball `B_r` in
the twelve adjacent-transvection generators of

`P=A8*A8 -> L_(F2)(1,2)^times`,

computes every image by exact binary Leavitt arithmetic, and hashes images
only after homogeneous refinement to a pool-wide common right-prefix depth.
Within every equal-image bucket it retains a spanning tree of word
differences.  Those differences generate every kernel element represented
by a word of length at most `2r`.

Each retained difference is independently evaluated and checked to be the
identity in the Leavitt algebra.  The calculation uses no floating-point
arithmetic.

## Results

The command

```text
python3 experiments/atlas_kernel_collision_enumerator.py --radius r
```

gave:

| `r` | complete kernel radius | distinct `P` ball | distinct Leavitt images | collision buckets | largest bucket | distinct tree differences | commutator constraints |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 13 | 13 | 0 | 1 | 0 | 0 |
| 2 | 4 | 129 | 109 | 20 | 2 | 20 | 220 exact |
| 3 | 6 | 1,227 | 795 | 300 | 5 | 264 | 3,128 exact |
| 4 | 8 | 11,599 | 5,503 | 2,893 | 41 | 2,734 | 32,756 exact |
| 5 | 10 | 109,399 | 36,971 | 23,731 | 119 | 27,256 | at most 327,072 |

The exact commutator count is requested with
`--deduplicate-constraints`.  It was omitted at radius five because retaining
all roughly three hundred thousand word keys is unnecessary for the kernel
enumeration itself.  The displayed upper bound is twelve times the number of
distinct tree differences.

## Consequences

1. The map is injective on the radius-one ball, and there is no nonidentity
   kernel element represented by an `X`-word of length at most two.
2. The first complete nonempty window is already small: twenty kernel
   generators and 220 distinct centrality constraints cover every kernel
   word through length four.
3. Global deduplication matters.  At radius five the raw bucket spanning
   trees contain 72,428 edges, but only 27,256 distinct free-product
   differences.  Thus image collisions recur coherently across many
   buckets rather than behaving like unrelated random coincidences.
4. The earlier optimizer's 648 constraints came from 54 hand-selected
   Steinberg words.  They are valid, but they are not one of these complete
   metric balls.  The radius-two list is the first rigorous small target for
   a complete-window optimization; radius three is the next one.

The enumeration does not decide whether the limiting normalized-HS energy
vanishes as the regular multiplicity grows.  It removes the algebraic
incompleteness of the finite constraint list and makes that analytic limit
the only remaining issue for each displayed window.

## Radius-two representation calibration

`atlas_complete_window_search.py` feeds the complete radius-two list into
the existing one-relative-unitary optimizer in the 15-point permutation
representation of each `A8` factor.  This is not the asymptotically regular
sector required by the criterion, but it is a cheap exact calibration.

The vectorized command

```text
python3 experiments/atlas_complete_window_search.py --radius 2 --inner-scan
```

exhausts all 20,160 inner relative alignments.  No alignment satisfies all
220 constraints.  The unique lexicographic optimum is the alignment encoded
by the `GL_4(F_2)` bit word 33060.  It satisfies 208 constraints exactly and
has

`mean trace = 0.9709090909`,
`RMS defect = 0.2412090757`,
`maximum defect = 1.0327955590`.

The twenty kernel generators in this window are cross-chart commutators of
adjacent transvections.  The best alignment kills eighteen of them exactly.
The two survivors are

`[p2_32,p1_23]` and `[p2_23,p1_32]`;                 `(ACW1)`

their aligned `GL_4(F_2)` values are the opposite transvections `e_31` and
`e_13`.  Precisely the twelve constraints asking these two survivors to
centralize the two factor generating sets fail.  Thus the classical optimum
has a clean structural description: it aligns the entire shortest
cross-commutation web except for one opposite-root pair, rather than using a
hidden central/projective value for the kernel words.

Starting the unrestricted `U(15)` max-focused optimizer at that alignment
and running four 600-step perturbations changed the best maximum defect only
to `1.032793451`, while slightly worsening the RMS defect.  Thus the best
classical alignment is also a very stiff stationary locus in the full
unitary space.  This is numerical evidence only: it neither proves a
dimension-15 lower bound nor addresses multiplicity growth.  Its value is
that the first complete window is already nontrivial even before the longer
Steinberg relations enter.

## Exact minimax theorem for inner regular mixtures

There is a separate, fully regular calculation.  Let `lambda` be the left
regular representation of `A8`.  For `h in A8`, use the relative alignment

`lambda(g)` on factor one and `lambda(hgh^(-1))` on factor two. `(ACW2)`

Every radius-two constraint then evaluates to a regular matrix `lambda(k)`.
Its normalized trace is one if `k=1` and zero otherwise, so its squared HS
defect is exactly zero or two.  A block direct sum of inner alignments is
therefore a probability distribution on the 20,160 rows of the exact
satisfaction matrix.

**Proposition (exact inner-mixture optimum).**  Among all such probability
distributions, the least possible worst failure probability is exactly

`2/7`.                                                     `(ACW3)`

Equivalently, the least possible worst normalized-HS defect is

`sqrt(4/7) = 0.7559289460...`.                            `(ACW4)`

**Computer-assisted proof.**  The exact primal certificate places weights

```text
bits       4680  6180  8580  16952  33060
numerator     1     1     2      1      2
```

over denominator seven.  Direct evaluation shows that every one of the 220
constraints fails with total numerator at most two.  For the converse, put
uniform weight `1/7` on constraints

`26, 38, 50, 96, 97, 98, 114`.                         `(ACW5)`

Every one of the 20,160 inner alignments fails at least two of these seven
constraints.  Hence, for any distribution on alignments, the average of the
seven failure probabilities is at least `2/7`; at least one constraint has
failure probability at least `2/7`.  This proves both bounds.

The `--inner-mixture` mode discovers the linear-program solution and then
rationalizes it.  It accepts the result only after checking both displayed
integer certificates directly against the exact Boolean satisfaction
matrix.  Thus no floating-point LP tolerance enters the proof.

The primal certificate gives a concrete canonical model with regular
multiplicity seven.  If `delta_(tree,2)` denotes the maximum over the 220
spanning-tree constraints used here, it gives the rigorous finite-window
upper bound

`delta_(tree,2) <= sqrt(4/7)`.                           `(ACW6)`

The matching lower bound applies only to direct sums of inner alignments.
It does not apply to arbitrary relative unitaries in the regular
representation, to outer automorphism alignments, or to other multiplicity
sectors.  Consequently it does not decide `delta_(tree,2)`, much less the full
hyperlinearity criterion.  It does prove that simply mixing classical inner
charts cannot drive even the first complete window to zero; a successful
model must use genuinely additional representation geometry.
