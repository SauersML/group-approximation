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
