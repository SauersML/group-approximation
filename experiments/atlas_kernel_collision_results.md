# Exact collision windows for the binary Leavitt atlas

Date: 2026-08-11

## Purpose

`atlas_kernel_collision_enumerator.py` implements Proposition 4 of
`notes/FALSE_RECURSIVE_ATLAS_EXHAUSTION.md`.  It enumerates the ball `B_r` in
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

## Exact minimax theorem for all regular automorphism mixtures

The graph automorphism

`theta(g)=(g^(-1))^T`                                  `(ACW7)`

is an outer automorphism of `GL_4(F_2) ~= A8`, and every automorphism of
`A8` is an inner automorphism or an inner automorphism followed by `theta`.
Thus the 20,160 inner alignments and their 20,160 outer partners exhaust all
classical automorphism alignments of the two regular factors.

The same exact Boolean minimax calculation over all 40,320 alignments gives:

**Proposition (exact full-automorphism optimum).**  Among all direct sums of
regular automorphism alignments, the least possible worst failure
probability on the 220 radius-two tree constraints is exactly

`3/11`.                                                    `(ACW8)`

Equivalently, the optimal worst normalized-HS defect in this whole sector is

`sqrt(6/11) = 0.7385489458...`.                          `(ACW9)`

The exact primal certificate has denominator eleven:

| bit word | coset | numerator |
|---:|:---:|---:|
| 4680 | inner | 2 |
| 6180 | inner | 1 |
| 16680 | inner | 1 |
| 33060 | inner | 3 |
| 4680 | outer | 3 |
| 33060 | outer | 1 |

Every constraint has failure numerator at most three.  A matching exact
dual certificate of denominator eleven is supported on constraints

```text
index       51  67  99  104  112  113  115  135  136
numerator    1   1   2    1    1    1    1    1    2
```

Every automorphism alignment has dual-weighted failure numerator at least
three.  Averaging proves that every probability distribution on the 40,320
alignments has some constraint with failure probability at least `3/11`.
The script verifies both integer inequalities against all rows before it
prints the certificate.

This closes the entire classical automorphism sector for the first complete
window.  Outer blocks provide a small but strictly positive improvement over
inner blocks; they do not create a vanishing sequence.  Any model witnessing
the recursive hyperlinearity criterion must therefore use relative
unitaries which are not block sums of intertwiners implementing
automorphisms of the two regular `A8` actions.

## Exact tensor-flip theorem and the first nonclassical boundary

There is a canonical nonclassical relative unitary which completely changes
the radius-two conclusion.  Write `K=A8`, let `L` be its left regular
representation on `ell^2(K)`, and define

`J delta_g = delta_(g^(-1))`.                              `(TF1)`

Then `J L_h J = R_h`, where `R_h delta_g=delta_(g h^(-1))` is the right
regular representation.  Hence the canonical model with relative unitary
`U=J` sends factor one to `L(K)` and factor two to `R(K)`.  The two factors
commute, although the two restrictions are still unitarily equivalent copies
of the regular representation.

For a free-product word `w`, let `p_i(w)` be the product in `K` of the
letters of `w` belonging to factor `i`, preserving their order and deleting
the letters from the other factor.  Commutation of the left and right
actions gives the exact formula

`pi_J(w) = L_(p_1(w)) R_(p_2(w))`.                       `(TF2)`

**Proposition (tensor-flip centrality test).**  For `q in K*K`, the following
are equivalent:

1. `pi_J(q)` centralizes both regular factor images;
2. `p_1(q)` and `p_2(q)` lie in `Z(K)`;
3. `p_1(q)=p_2(q)=1`.

**Proof.**  The right action commutes with every left translation, so
commuting `L_a R_b` with all `L_h` is equivalent, by faithfulness of `L`, to
`a in Z(K)`.  Symmetrically, commuting it with all `R_h` is equivalent to
`b in Z(K)`.  Finally `A8` is centerless.  This proves all equivalences.

Consequently, the projection pair `(p_1(q),p_2(q))` is an exact, finite
certificate for whether the tensor-flip model satisfies all twelve
centrality constraints attached to `q`.  Applying this test to the complete
meet-in-the-middle tree lists gives:

| half-radius `r` | complete kernel-word radius | tree generators | nontrivial projection pairs, with multiplicity |
|---:|---:|---:|---:|
| 2 | 4 | 20 | 0 |
| 3 | 6 | 264 | 0 |
| 4 | 8 | 2,734 | 0 |
| 5 | 10 | 27,256 | 234 |

Thus `U=J` is an **exact zero-energy canonical regular model for every
complete kernel window through word length eight**.  In particular, the
positive minimax gaps `(ACW3)` and `(ACW8)` are genuinely restrictions of
the classical automorphism sectors, not lower bounds for arbitrary relative
unitaries.

At word length ten the first obstruction appears, but it is highly
compressed.  Among the 234 failing tree generators there are only 24
distinct ordered projection pairs in `A8 x A8`; 116 have pattern
`(1,nonidentity)`, 102 have pattern `(nonidentity,1)`, and 16 have both
projections nonidentity.  The remaining 27,022 tree generators still vanish
under `(TF2)`.  Therefore the next mathematical problem is finite and
structural: deform or amplify the left-right model so that these 24 ordered
pairs become asymptotically central without losing the two regular factor
characters.  No further enumeration of the original Leavitt kernel is
needed to locate the first obstruction.

The exact 24 ordered pairs and their multiplicities are emitted by the
enumerator and committed in
`experiments/atlas-kernel-radius5-summary.json`.  Regenerate the compact
artifact with

```text
python3 experiments/atlas_kernel_collision_enumerator.py --radius 5
```

The same artifact records an exact support audit.  Among the 234 failing
words, 210 lie entirely in `H*H`: 104 have projection pattern `(1,b)`, 90
have `(a,1)`, and 16 have `(a,b)`, with displayed nonidentity entries.
Consequently the tempting coset-multiplicity ansatz
`U=(I_(ell^2 H) tensor V)J`, `V in U(120)`, is rigid.  It keeps the two
`H`-actions commuting, so each of these words evaluates as
`L_a U L_b U^*`; a selected `H`-generator exposes a nonidentity regular
commutator of defect `sqrt(2)`.  This exact filter prevents a large but
mathematically futile manifold optimization.

Auditing all 15 point and 15 hyperplane stabilizers gives the constructive
counterpoint.  Eighteen contain no failing word entirely in `M*M`.  Since
each such `M` has order 1,344 and index 15, the ansatz
`U=(I_(ell^2 M) tensor V)J` retains the exact regular factor restrictions
while reducing the live variable to `V in U(15)`.  It is not ruled out by
the support certificate.  This is a regular-representation multiplicity
deformation, not the earlier 15-point representation optimizer.

## First implicit index-15 deformation search

`atlas_stabilizer_coset_search.py` implements this ansatz without forming a
`20160 x 20160` matrix.  Left and right translations are permutations of
the regular basis, while `V` acts in 1,344 identical `15 x 15` blocks.  The
script differentiates a fixed Hutchinson trace estimate through
`V=exp(A-A^T)` and samples half exposed boundary constraints and half exact
tensor-flip controls.

At `V=I`, that balanced batch has exact mean squared defect one: exposed
regular commutators contribute two and controls contribute zero.  Two small
bounded runs gave:

| seed | initial rotation scale | batch | iterations | sampled loss path |
|---:|---:|---:|---:|:---|
| 0 | 0.02 | 4 | 10 | `1.02588 -> 1.00026` |
| 1 | 0.20 | 8 | 30 | `1.24910 -> 1.13241` |

Both flows move toward the tensor-flip value rather than below it.  This is
only stochastic local evidence, not a lower bound and not a reason to rule
out the index-15 family globally.  It is enough to stop seed sweeps.  The
next useful computation is an exact induced-coordinate Hessian at `V=I`,
followed by a rational SOS certificate if the Hessian is positive on every
non-gauge direction.  Raw results are in
`atlas-stabilizer-coset-seed0.json` and
`atlas-stabilizer-coset-seed1.json`.

The 24 pairs themselves have an exact group-theoretic compression.  Their
six one-sided nonidentity entries are the same in the two coordinates.  Four
are adjacent elementary transvections in the upper-left `3 x 3` block; the
other two are products which recover the two remaining opposite-corner
transvections after multiplication by an adjacent one.  Hence these six
matrices generate

`H={diag(A,1):A in GL_3(F_2)} ~= GL_3(F_2)`, `|H|=168`. `(TF3)`

Every coordinate of every residual pair lies in `H`.  Conversely, the pair
list contains `(h,1)` and `(1,h)` for all six displayed generators.  It
follows immediately that the subgroup generated by all 24 pairs is exactly

`H x H ~= GL_3(F_2) x GL_3(F_2)`.                       `(TF4)`

This is more than a count reduction: the first obstruction is supported on
a proper point-and-hyperplane stabilizer in each `A8=GL_4(F_2)` factor.  In
particular

`Res_H^(A8)(lambda_A8) = 120 lambda_H`,                 `(TF5)`

so the next construction has a canonical 120-dimensional multiplicity
space on which to deform the tensor flip while controlling the rank-three
corner.

There is also a sharp no-go for the obvious deformation.  On
`ell^2(A8) tensor V`, let `D=directsum_g D_g` be any block-diagonal unitary
and take

`U=D(J tensor 1_V)`.                                    `(TF6)`

Every word remains block-monomial, and its base permutation is still
`L_(p_1(w)) R_(p_2(w))`; the fiber gauges affect only the nonzero matrix
blocks.  If `p_1(w)!=1`, some selected factor-one generator `x` has
`[x,p_1(w)]!=1`, because those generators generate the centerless group
`A8`.  The base permutation of `pi_U([x,w])` is then a nonidentity regular
translation and has no fixed points.  Its normalized trace is exactly zero,
independently of `V` and of all `D_g`, so

`||pi_U([x,w])-1||_2=sqrt(2)`.                          `(TF7)`

The same argument uses factor two when only `p_2(w)` is nontrivial.  Hence
every block-phase or matrix-cocycle twist of inversion has maximum defect at
least `sqrt(2)` on the radius-ten window.  The next model must change the
permutation support or be genuinely nonmonomial; phase decoration alone
cannot repair the rank-three corner.
