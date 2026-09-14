---
rg: 2
id: elementary-group-lef-growth-separates-subshifts
kind: claim
title: LEF growth of the measure-side Kazhdan simple groups is controlled by the return-time function of the subshift and separates different Diophantine types
artifacts:
  - research/artifacts/un-open-7-coarse-geometry-2026-09-13.md
refuted_by: [sturmian-elementary-group-lef-growth-is-exp-r-squared]
---

**REFUTED as stated** (sk-lef-growth, 2026-09-13, UNREVIEWED): the LEF growth class is `exp(r^2)` for every Sturmian slope. The isomorphism conclusion stays open; see Attempts.

For a LEF group `S` with finite generating set `T`, define the **LEF growth**

`F_{S,T}(r) = min { |H| : H finite, and some φ: B_T(r) -> H is injective and satisfies
φ(xy) = φ(x)φ(y) whenever x, y, xy ∈ B_T(r) }`.

Changing `T` rescales `r` by a bounded factor, so the growth class of `F_S` modulo
`r ↦ Cr` is an isomorphism invariant of `S`. This is the LEF analogue of residual
finiteness growth.

**Claim.** For `S_X = EL_n(LC(X, F_q) ⋊ Z)/Z` with `X` an infinite minimal subshift, the
growth class of `F_{S_X}` is determined, up to the usual rescaling, by the return-time
function of `X`. Consequently Sturmian subshifts whose slopes have different Diophantine
type give non-isomorphic groups `S_X`.

**Why it is worth deciding.** `lef-infinite-simple-groups-are-qi-rigid` shows the whole
measure side is uniformly far from finite presentations, but nothing in the program
distinguishes measure-side rungs **from each other**. A positive answer would upgrade the
answer to Pestov 9.1 from "such a group exists" to "the dynamics is visible in the coarse
geometry of the group", and would produce a continuum of pairwise non-isomorphic infinite
simple Kazhdan LEF groups indexed by Diophantine type.

## Attempts

- **Refuted in its LEF-growth form (sk-lef-growth, 2026-09-13, UNREVIEWED).**
  `sturmian-elementary-group-lef-growth-is-exp-r-squared`: for every irrational slope `α`, `L_(X_α)(r) = exp(Θ(r^2))`, with
  constants independent of `α`, although the return-time function of `X_α` depends on `α`. So the LEF growth class does
  not separate Diophantine types.
  - Upper bound: a covering closed walk in the Sturmian Rauzy graph has length `≤ 2n+2`.
  - Lower bound: two letter conditions at distance `q_n ± 1` cut out a clopen set with no returns below `q_(n+1)`, whose
    transvections cost `O(m)` letters. The unitriangular relations of the tower copy of `GL_(3(2m+1))(F_2)` then force a model
    of order `≥ 2^(d(d−1)/2)`.
  - This answers "any argument has to extract dynamical data from an abstract ball-injective partial homomorphism" (below):
    transport the bounded-length unitriangular relations and detect the kernel on the central transvection.
  - The isomorphism conclusion ("non-isomorphic groups") stays open. It needs other invariants; see
    `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.
- **Upper bound, conditional and close to done.** Suppose the `r`-ball of
  `R_X = LC(X, F_q) ⋊ Z` is carried by a Kakutani–Rokhlin tower model
  `W_r -> M_{N(r)}(F_q)`, injective and multiplicative on the window `W_r`, with `N(r)`
  the tower height. This is what the return-word construction of
  `minimal-subshift-algebra-is-simple-lef-ring` supplies. Then `EL_n` of the model is the
  finite group `EL_{n N(r)}(F_q)` and
  `F_{S_X}(r) <= |EL_{n N(r)}(F_q)| <= q^{(n N(r))^2}`.
  For a Sturmian subshift of slope `α` the return times are governed by the continued
  fraction expansion of `α`, so different Diophantine types give different upper bounds.
  *What is missing:* the precise dictionary from group ball radius `r` to ring window
  `W_r` to tower height `N(r)`, which the artifact does not carry out.
- **Lower bound, the crux.** The claim needs that *no* smaller finite group models the
  `r`-ball, by any route and not only by towers. *Where it dies:* a finite model of the
  `r`-ball of `EL_n(R_X)` need not come from a ring model of a window of `R_X`, so there
  is no evident route from a small group model back to a short return word. Any argument
  has to extract dynamical data from an abstract ball-injective partial homomorphism.
- **Separation without exact growth.** Weaker and perhaps easier: show only that some
  pair of slopes gives non-isomorphic groups, for instance by comparing a single
  numerical invariant extracted from `F_{S_X}` rather than the whole growth class.
- **Calibration.** Any proposed lower bound must be compatible with the paradox side,
  where `S` is not LEF at all and `F_S` is undefined; so the invariant cannot be
  formulated in a way that silently assigns it a value there.
