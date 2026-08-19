# Perfect binary pairings have a dimension-free transport error floor

Date: 2026-08-13

## 1. Outcome

The finite paired-radical endpoint admits a direct robust formulation which
does not require constructing a complex Fourier unitary, deleting its
constant mode, or separately proving that four pullback operators are
contractions.

Let `V,W` be nonzero finite binary vector spaces of the same cardinality
`N`, and let

```text
b : V times W -> F2
```

be a perfect bilinear pairing.  For maps `R : V -> V` and `L : W -> W`, put

```text
eps(R,L) = Pr[b(Rv,Lw) != b(v,w)],
zeroErr(R,L) = Pr[b(Rv,Lw) != 0],                  (RPF1)
```

where `(v,w)` is uniform on `V times W`.

For arbitrary maps `R0,R1,L0,L1`, one has

```text
zeroErr(R0,L1) + 4 eps(R0,L0) + 4 eps(R1,L1)
  >= (N-1)/(2N).                                    (RPF2)
```

Consequently

```text
max(zeroErr(R0,L1),eps(R0,L0),eps(R1,L1))
  >= (N-1)/(18N)
  >= 1/36.                                           (RPF3)
```

This is a dimension-independent robust form of the exact finite theorem in
`TRUE_FINITE_PAIRED_QUOTIENT_OBSTRUCTION.md`.

## 2. Approximate diagonal transport is close to a permutation

Fix `R,L` and write `eps=eps(R,L)`.  For each `v`, let `E(v)` be the number
of labels `w` on which

```text
b(Rv,Lw) != b(v,w).
```

Consider a fiber `F` of `R` with cardinality `s>=2`.  For distinct
`v,v'` in `F`, the two predicted rows are identical, while perfectness of
`b` says that the target rows `b(v,-)` and `b(v',-)` disagree at exactly
`N/2` labels.  Therefore

```text
E(v)+E(v') >= N/2.                                  (RPF4)
```

Sum `(RPF4)` over all unordered pairs in `F`.  Each `E(v)` occurs `s-1`
times, so

```text
sum_(v in F) E(v) >= sN/4.                          (RPF5)
```

Summing over the nonsingleton fibers gives

```text
N-card(im R) <= 4 eps N.                            (RPF6)
```

Choose one representative in every fiber of `R` and biject the remaining
inputs with the missing outputs.  This produces a permutation `Rbar` which
differs from `R` on at most `4 eps N` points.  Applying the column version of
the same argument produces a permutation `Lbar` with the same bound.

Applied to the two diagonal relations, this gives

```text
Pr[R0 != R0bar] <= 4 eps(R0,L0),
Pr[L1 != L1bar] <= 4 eps(R1,L1).                    (RPF7)
```

No operator norm, singular-value truncation, or condition-number estimate is
used.

## 3. The crossed-zero table cannot survive the repair

For permutations `R0bar,L1bar`, the table

```text
b(R0bar v,L1bar w)
```

is just a row-and-column permutation of the original perfect pairing table.
The zero vector contributes no ones, and every one of the other `N-1` rows
contains exactly `N/2` ones.  Its one-density is therefore

```text
(N-1)/(2N).                                         (RPF8)
```

Changing the left map on a fraction `deltaV` of inputs and the right map on
a fraction `deltaW` changes at most `deltaV+deltaW` of the whole table.
Equations `(RPF7)--(RPF8)` give `(RPF2)`, and `(RPF3)` follows because the
three coefficients in `(RPF2)` sum to nine.

## 4. Convex extension under a common classical coupling

The same floor holds after randomizing the deterministic maps on one common
classical probability space.  Let

```text
omega -> (R0_omega,R1_omega,L0_omega,L1_omega)
```

be a probability distribution on map quadruples, and define each
error by first sampling the same `omega` and then sampling the source labels
uniformly.  For example,

```text
eps00 = Pr[b(R0_omega(v),L0_omega(w)) != b(v,w)].    (RPF9)
```

Then `(RPF2)` holds at every atom of the law.  Averaging gives the identical
inequality

```text
eps01 + 4 eps00 + 4 eps11 >= (N-1)/(2N).            (RPF10)
```

The common-law qualification is essential.  If two atomic decompositions of
a finite Hilbert space have `N` atoms of a common rank `m`, the normalized
squared Hilbert--Schmidt block masses of a unitary do form a doubly stochastic
matrix.  Those marginal matrices alone do not determine the joint coupling
which measures a two-transport relation.

In fact, if the left and right targets are sampled independently from two
doubly stochastic kernels, they are jointly uniform after averaging the
source labels, so the crossed one-density is already exactly
`(N-1)/(2N)`.  The Lean theorem
`independentKernelOneMass_perfect` records this stronger elementary fact.
The reason it does not finish the microstate argument is precisely that
independence has not been extracted.  See
`FALSE_INDEPENDENT_BISTOCHASTIC_KERNEL_EXTRACTION.md` for the two-point
counterexample and the corrected common-latent-permutation gate.

The finite quotient dimension need not be constant across latent atoms.
For every nonzero binary pairing fiber, `N>=2`, so

```text
(N-1)/(2N) >= 1/4.                                  (RPF10a)
```

Apply `(RPF10)` separately on each atom with its own radical quotients and
then average.  The resulting global bound is

```text
E eps01 + 4 E eps00 + 4 E eps11 >= 1/4.              (RPF10b)
```

Thus the extraction theorem does not need to select a single quotient rank
of positive trace.  It may retain a finite bundle of arbitrary nonzero
ranks, provided the three edge laws glue over the same latent atom.  The
convex step is formalized source-first as
`one_fourth_le_weighted_three_error`; it was not compiled in this iteration.

## 5. Formalization status

`GroupApproximation/Leavitt/RobustPairedQuotientFloor.lean` now formalizes
the gauge-free table endpoint and the canonical permutation repair.  Its
arithmetic theorem, `robust_floor_of_permutation_repairs`, proves the exact
integer inequality

```text
N(N-1) <= 2 e01 + 8 e00 + 8 e11,
```

from the two repair bounds `N*dR <= 4*e00`, `N*dL <= 4*e11` and the perfect
pairing one-count.  The supporting theorem
`card_oneSet_repaired_le` kernel-checks the dimension-free fact that changing
`dR` rows and `dL` columns changes at most `N*dR+N*dL` table entries.

The new repair layer defines `collisionSources R` to be the sources in
non-singleton fibers of `R`.  It constructs `repairMap R`, a permutation which
agrees with `R` away from that set, and proves

```text
#{v : repairMap R v != R v} <= #collisionSources R.  (RPF11)
```

The theorem `collision_pair_charge` also formalizes the local content of
`(RPF4)`: if two distinct sources collide and distinct perfect-pairing rows
differ on exactly `N/2` columns, then their two row-error counts have doubled
sum at least `N`.  Finally, `robust_floor_of_collision_budgets` wires the
canonical repairs directly into the robust floor.  Thus no unspecified
permutation repair remains.

The global fiber summation is now formalized as
`collisionSources_mul_le_totalRowMismatch`:

```text
N * #collisionSources R <= 4 * totalDiagonalMismatch. (RPF12)
```

The proof sums `collision_pair_charge` over all ordered off-diagonal pairs
inside each non-singleton fiber.  If the fiber has size `s`, every row-error
term occurs exactly `2(s-1)` times.  Cancelling the positive factor `s-1`
gives the optimal factor four, and summing over target fibers gives `(RPF12)`.
The generic double-counting identity is the theorem `sum_offDiag_pairCost`.

The theorem `robust_deterministic_floor` now combines both diagonal collision
budgets with the crossed-table estimate.  Its conclusion is the full integer
form of `(RPF2)` for deterministic transports.  Thus the deterministic finite
combinatorics has no remaining repair hypothesis.  The independent
bistochastic endpoint is also formalized and is stronger than needed.  The
common-law averaging theorem is
`robust_floor_of_common_latent_maps`; it keeps the shared latent variable
explicit in all three error terms.  The
genuinely research-level gate is the matrix-coordinate extraction of common
paired labels together with a common classical coupling of all four
transports.

## 6. Gain for the hyperlinear program

The previous robust-radical gate asked for a normalized complex Fourier
unitary, near-bijective arrows, removal of two trivial modes, invariance of
the reduced sectors, and three contraction estimates.  The Hamming theorem
shows that all of that is unnecessary once a finite perfect-pairing label
model with uniform counting measure has been extracted.

The strictly smaller live theorem is now:

> From one canonical regular-margin normalized-HS atlas microstate, extract
> finite binary label spaces with a perfect pairing and a common classical
> latent-map lift of the four transports for which the two diagonal
> mismatch rates and the crossed-zero rate tend to zero.

The fixed floor `1/36` then gives the contradiction directly.  Partial maps
are harmless: extend them arbitrarily on their bad sets, which only adds the
bad-set density to the three errors.

This still does not prove nonhyperlinearity.  The unresolved step is the
common-coordinate extraction and classicalization of the three pairwise
transport couplings.  Four bistochastic marginals do not suffice.  What has
been removed is the separate Fourier-flatness, near-bijectivity, and
trivial-mode analysis after a common classical lift has been extracted.

The existing four-cut raw coefficient packet does not itself instantiate
this theorem.  Its comb transition table is exactly Fourier-flat: after
conditioning on the transported carrier, every raw label sends mass `1/4`
to every transported label.  Thus it is maximally nondeterministic and does
not satisfy either diagonal error hypothesis.  The required perfect-pairing
kernels must come from the deeper multiplication/radical quotient, not from
the ambient `C2^2` coefficient cuts alone.
