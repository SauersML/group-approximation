# Perfect-overlap elimination of the first atlas boundary

Date: 2026-08-11

> **Status.** The scan and its 178 certified zero words remain authoritative.
> The remaining 56 words were subsequently reduced to the four cyclic
> survivor classes `11,30,44,55`; see
> `FALSE_ATLAS_CHART_FILLING_WIDTH.md`.  The “next target” below is the
> historical handoff from this scan, not the current four-class boundary.

## 1. Purpose

The local Clifford word from `FALSE_LOCAL_CLIFFORD_ATLAS.md` carries a
macroscopic projective phase on a truncated relation window, but
`FALSE_CLIFFORD_TORSION_GATE.md` proves that the phase dies in the full
central cover.  The proof uses a reusable mechanism: transport every letter
to one scalar chart, and force equality of the competing lifts on perfect
overlaps.

`experiments/atlas_perfect_overlap_scan.py` applies that mechanism to all 234
kernel words at the first tensor-flip boundary.  Its positive answers are
exact proofs in the central kernel.  Its negative answers are only candidate
survivors, so the script also gives an exact all-depth obstruction when no
common scalar chart can exist.

## 2. The perfect-overlap certificate

Let

\[
 C_1=(01,1,000,001),\qquad C_2=(00,1,010,011)          \tag{1}
\]

be the original four-leaf charts.  Suppose a kernel word (w\in R) has a
complete prefix code (D), with (|D|\geq5), satisfying the following two
conditions.

1. Every letter of (w) is represented as a scalar matrix in
   (G_D\cong GL_{|D|}(\mathbb F_2)).
2. For every support block of every letter, there is a uniform refinement of
   its original chart whose overlap with (G_D) contains that block in the
   derived subgroup of the overlap.

Then (w=1) in (P/[P,R]).  Indeed, (G_D) is superperfect and has a unique
lift to every central extension of (Q).  The original (A_8) chart lift
agrees with the lift of each uniform refinement because (A_8) is perfect.
The two refined lifts then agree on the selected support block because their
quotient is a central character and the block lies in the derived subgroup
of the overlap.  Thus every letter of (w) equals its (G_D)-lift.  Their
product is the lift of the identity matrix in (G_D), hence is one.

The finite test is particularly simple.  If an active support component has
(r) original leaves and its common descendant suffix code has (m) leaves,
the overlap contains (GL_{rm}(2)).  This group is perfect for (rm\geq3).
The only remaining case is (GL_2(2)\cong S_3), where the test accepts
exactly its derived subgroup of order three.  All arithmetic, including the
final product in (GL_{|D|}(2)), is exact over \(mathbb F_2\).

## 3. An all-depth obstruction to a common scalar chart

Every common refinement of `(1)` can be written in two ways.  Use nonempty
finite complete suffix codes

\[
 \mathcal A,\mathcal B,\mathcal C,\mathcal D,
 \mathcal E,\mathcal F,\mathcal G
\]

so that the first chart has suffix codes

\[
 (\mathcal A,\mathcal B,\mathcal C,\mathcal D)
\]

and the second has

\[
 (\mathcal E,\mathcal B,\mathcal F,\mathcal G).
\]

Comparing the two decompositions in the cylinders (01) and (00) gives

\[
 \mathcal A=0\mathcal F\mathbin\sqcup1\mathcal G,
 \qquad
 \mathcal E=0\mathcal C\mathbin\sqcup1\mathcal D.    \tag{2}
\]

In particular, their positive cardinalities satisfy

\[
 a=f+g,\qquad e=c+d.                                  \tag{3}
\]

If a matrix (M=(m_{ij})) from one original chart is represented on the
common refinement, then the suffix codes at (i) and (j) must be equal
whenever (m_{ij}=1).  The word therefore gives a finite union-find problem
on the seven variables in `(2)`.  After the forced identifications, either
equation in `(3)` having coefficients of only one nonzero sign is an exact
contradiction: all suffix-code cardinalities are positive.

This is not a bounded-depth heuristic.  It proves that no finite common
scalar chart exists at any depth.

## 4. Complete radius-ten result

The bounded discovery pass enumerated every refinement of the least common
five-leaf code through twelve leaves.  There are

\[
 1,5,20,75,275,1001,3640,13260
\]

codes at leaf counts (5,ldots,12), respectively.  On the 234 exact
radius-ten tensor-flip failures it found:

| outcome | words |
|---|---:|
| perfect-overlap certificate | 178 |
| no certificate | 56 |

The 178 certified words split by their smallest discovered chart size as

\[
 93\text{ at size }6,qquad
 77\text{ at size }8,qquad
 8\text{ at size }10.                                \tag{4}
\]

None of the remaining 56 words has a common chart through twelve leaves.
More decisively, every one has the exact cardinality obstruction from
Section 3.  After quotienting the seven suffix variables by its matrix
support equalities, every survivor has the same nonzero coefficient pattern

\[
 (-1,0),\qquad(0,-1),                                \tag{5}
\]

up to zero columns and reordering.  Thus both equations in `(3)` would force
a positive cardinality to vanish.  No one of the 56 words lies in any common
scalar chart, regardless of depth.

The 56 words occupy only eight ordered tensor-flip projection classes.  Four
classes have multiplicity eight and four have multiplicity six.  A shortest
representative in every class has free-product length eight; the other six
representatives have length nine.  The subgroups generated by the letters of
a representative have orders (4) and (8) in the two (A_8) factors
(with the roles reversed for the opposite orientations).  Thus the remaining
boundary is a small two-primary incompatibility, not a diffuse (A_8\times
A_8) phenomenon.

Run the exact scan with

```text
python3 experiments/atlas_perfect_overlap_scan.py \
  --radius 5 --max-leaves 12 --boundary-only --summary-only
```

The radius-five collision enumeration and every matrix product are exact;
floating point is not used.

## 5. Consequence and next target

This calculation removes 178 of the 234 first-boundary words from the search
for a central survivor and independently rederives the death of the local
Clifford word.  It does **not** prove that any of the 56 incompatible words
is nonzero in (R/[P,R]).  A perfect-overlap chain using several intermediate
charts, or another global relation, may still kill them.

The next FALSE computation should work with one representative of each of
the eight projection classes.  For each representative it should determine
the central phase spectrum compatible with two honest (A_8) chart
representations, then test that phase against additional exact atlas
relations.  The relevant local groups have orders only (4) and (8), so
exact character restriction and finite presentation calculations should
precede any continuous unitary optimization.
