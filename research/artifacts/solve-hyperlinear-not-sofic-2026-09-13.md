# Is every hyperlinear group sofic? Mechanism audit and the simple-group dichotomy

Lane `solve-hyperlinear-not-sofic`, 2026-09-13. Target: `hyperlinear-nonsofic-group`
(Pestov Question 3.4, separation side). Pin `09259036f`. Nothing was run. Unreviewed.

## 0. Summary

- **New claim.** `infinite-simple-group-hs-stable-iff-nonhyperlinear`, ESTABLISHED through a
  direct proof. Let `S` be an infinite simple group with no nontrivial finite-dimensional unitary
  representation, which covers every finitely generated one. Then `S` is not hyperlinear exactly
  when every asymptotic HS representation collapses, and exactly when `S` is strictly, or
  flexibly, HS stable.
- **Q3.4 reading.** With `infinite-simple-group-permutation-stable-iff-nonsofic`, such `S` is a
  hyperlinear nonsofic group exactly when every almost action collapses but some asymptotic
  representation does not.
- **Three proposed mechanisms are dead.** Trace statistics (§2), stable witnesses (§3) and
  diagonal-lamp models of the Kun--Thom wreath (§4). Main already settles each; this file
  collects the reasons.

## 1. Where the separation question stands on main

- Root `hyperlinear-nonsofic-group`: about 25 routes. Its converse `hyperlinear-implies-sofic`
  has 12 routes, two of them marked dead.
- **Candidates.** `binary-leavitt-unit-group-hyperlinear` (first nonsofic group),
  `boundary-action-simple-kazhdan-group-is-hyperlinear`, `coset-wreath-is-hyperlinear`, Thompson
  F and V, the Fournier--Facio group. Hyperlinearity of each is open.
- **Complexity form.** `sofic-recognition-under-hyperlinear-promise-dichotomy`.
- **Frame form.** `hyperlinear-groups-admit-masa-normalizing-microstates`, equivalent to Q3.4,
  and `monomially-hyperlinear-groups-are-sofic` (OPEN).

## 2. Trace statistics cannot separate

The proposed mechanism: permutation characters are nonnegative, unitary characters need not
be, so look for a group whose approximations of the regular trace need characters bounded
below zero.
- **It fails at the limit.** Any approximation of `tau_reg` has `chi_n(g) -> 0` for `g != 1`. A
  negative bound away from zero contradicts convergence.
- **It fails at every finite stage.** `sigma = phi ⊗ conj phi` has
  `tr sigma(g) = |tr phi(g)|^2 >= 0` and at most twice the defect (identity (TE) of the proof
  route). Every hyperlinear group has asymptotic representations with real, nonnegative
  characters converging to `delta_e`.
- **Already on main.** `character-domination-collapse-equivalences` formalizes
  `C_perm <= C_fd`: permutation domination follows from unitary domination.
- **Consequence.** A gap must live in non-tracial data (frames, matrix entries, multiplicity
  spaces), not in any functional of characters at finitely many group elements.

## 3. HS-stable witnesses cannot separate

The proposed mechanism: a group that is HS stable with the regular trace approximable, while its
permutation almost actions are forced to collapse.
- **Dead.** A finitely generated hyperlinear flexibly HS-stable group is residually finite
  (`hyperlinear-flexibly-hs-stable-group-is-residually-finite`), hence sofic.
- **For simple groups** the new claim sharpens this: HS stability *is* nonhyperlinearity. Any
  simple separation witness must be HS unstable.

## 4. Diagonal lamps on the Kun--Thom wreath are covered by the EX soft-kernel theorems

- **The idea.** In `W = F_2[G/Gamma] ⋊ G`, realize lamps as `±1` diagonal matrices. They commute
  exactly, trace cancellation replaces derangement, and the permutation part is a sofic model of
  the linear group `G`.
- **Covered.** This is a monomial HS model (block size 1).
  `research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md`, Theorem 7: every
  monomial HS model of `W` kills `K_even = Rad_sof(W)`, whatever the phases. Part 3, Theorem 9,
  extends this to any fixed block size, and part 4, Theorem 12, to the Clifford covers.
- **Heuristically the same obstruction** as Kun--Thom Corollary D (quoted in
  `kun-thom-nonsofic-wreath`): generalized Bernoulli actions over infranormal Kazhdan pairs are
  not sofic. A `Gamma`-invariant `±1` coloring is a `Gamma`-fixed function, and Theorem C forces
  it to be `G`-invariant. I did not check whether the diagonal model literally gives a sofic
  action in Kun--Thom's sense.
- **Threshold.** Part 3 states that unbounded block size stays universal. So any hyperlinear
  model of `W` rotates multiplicity spaces of unbounded rank.

## 5. The simple-group dictionary

For `S` infinite simple with no finite-dimensional unitary representations (e.g. `EL_4(L)`,
`S_∂`, Thompson `V` and `T`, the commutator subgroup of the Lodha--Moore group):

| property | collapse statement | main node |
|---|---|---|
| nonsofic | every almost action `S -> Sym(k_n)` collapses | `infinite-simple-group-permutation-stable-iff-nonsofic` |
| nonhyperlinear | every asymptotic representation `S -> U(d_n)` collapses | `infinite-simple-group-hs-stable-iff-nonhyperlinear` |
| hyperlinear nonsofic | first collapses, second does not | both |

Every nontrivial homomorphism of `S` into a tracial unitary group is injective with
`|tau(g)| < 1` off the identity. So one noncollapsing asymptotic representation already gives
regular approximations, by conjugate tensor powers. No regularity has to be built in.

## 6. Exact gap

- **For a simple candidate.** Exhibit one asymptotic representation of `S` that does not
  collapse, while every almost action collapses. For every simple nonsofic group on main, the
  second half is established. The first half is equivalent to hyperlinearity and is open for
  each of them.
- **For the Kun--Thom wreath.** A hyperlinear model whose frames escape every bounded rank.
- **The known obstacle.** No construction of a noncollapsing asymptotic representation is
  known for any minimally almost periodic simple group containing Kazhdan subgroups with
  one-sided compressions. `research/artifacts/hyperlinear-nonsofic-l-times-2026-09-12.md` §0
  records why models of `L^x` stay at distance `sqrt 2` from genuine representations on every
  minimally almost periodic subgroup.

## 7. Sources

- **Not re-pinned here.** Pestov's survey, Elek--Szabó, Becker--Lubotzky and
  Arzhantseva--Păunescu. Existing pins on main: `ex-q34-frame-extraction-2026-09-12.md`,
  `ex-open-status-2026-09-12.md`.
- **Quoted as main records them.** Kun--Thom Theorems A, C, E and Corollary D, from
  `kun-thom-nonsofic-wreath` (import of arXiv:2608.06222).
- **Novelty.** The new claim is elementary, and no priority is claimed.
