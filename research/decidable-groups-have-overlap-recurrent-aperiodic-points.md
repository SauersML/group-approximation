---
rg: 2
id: decidable-groups-have-overlap-recurrent-aperiodic-points
kind: claim
title: Every infinite finitely presented group with solvable word problem has a computable hyperaperiodic point whose central patches recur with margin (overlap recurrence)
distinct_from:
  decidable-fp-groups-have-effective-minimal-free-subshifts: that is (M2), the existence of an effective minimal free subshift, which is equivalent to a margin covering tower with arbitrary finite families L_n; this is the one-patch extreme |L_n| = 1, a strictly more rigid sufficient condition that may fail even where (M2) holds.
  covering-towers-iff-effective-minimal-free-subshifts: that is the established equivalence and the corollary that an overlap-recurrent hyperaperiodic point gives (M2); this is the open existence statement for such points.
  rf-toeplitz-subshift-has-computable-language: that builds Toeplitz points whose patches return along finite-index subgroups; by Lemma T of the covering-towers route, such subgroup returns can never supply the margin density asked for here.
artifacts:
  - experiments/overlap-recurrence-2026-09-17/overlap_margin_z.py
  - experiments/overlap-recurrence-2026-09-17/overlap_margin_z.out.txt
---

**OPEN.** Premise of route
`effective-minimal-free-subshifts-via-overlap-recurrence`.

**Statement.** Let `Λ` be an infinite finitely presented group with solvable
word problem. Then there are a finite alphabet `A`, a computable point
`y ∈ A^Λ`, and computable sequences `R_n` and `m_n` such that:
- the sequences satisfy `0 ≤ m_n ≤ R_n ≤ R_{n+1}`, `m_n → ∞` and
  `R_n − m_n → ∞`;
- **(OC)** for every `n` and every `g ∈ Λ`, some `h` with `d(g,h) ≤ R_n − m_n`
  has `y(μh) = y(μ)` for all `μ ∈ B(R_n)`;
- **(A)** for every `s ≠ 1` there is `R(s)` such that for every `λ` some
  `μ ∈ B(R(s))` has `y(μλ) ≠ y(μsλ)`.

The notation is that of `covering-towers-iff-effective-minimal-free-subshifts`,
with `d(x,z) = |xz^{-1}|`.

**Why it matters.** By the Corollary of
`covering-towers-iff-effective-minimal-free-subshifts`, the statement implies
(M2) for `Λ`.
- The orbit closure of `y` equals the explicitly defined set `Y_OC`, so no
  recurrence modulus has to be computed.
- Its forbidden set is decidable.
- By the Supplement, (OC) needs only the finite checks (IC_n) on nested patches.

**Evidence.**
- *For, over `Z`.* The prefix patches of the Fibonacci and Tribonacci fixed
  points return with maximal gap well below the patch length (artifact).
  - Fibonacci: at length `L = 2580` the max gap is `1597`, and
    `min gap/L ≈ 0.62` over the lengths tested.
  - Tribonacci: at `L = 2027` the max gap is `1705`, and `min gap/L ≈ 0.84`.
  - These are one-sided prefixes, a proxy for the two-sided ball condition.
  - The Sturmian instance of (M2) over `Z`, through direction 1 ⇒ 2 of the
    Theorem, gives only a tower with general families `L_n`, not `|L_n| = 1`.
  - So the `Z` case of (OC) is supported numerically, not proved here.
- *Against, as a general mechanism.* The same test fails, with `max gap ≥ L` at
  every length tested, for:
  - Thue--Morse (`gap/L ≥ 2`);
  - period doubling (`≥ 1.003`);
  - Chacon (`≥ 1.004`).
  - The first two are Toeplitz or odometer type, and Chacon is weakly mixing.
- *Obstruction.* Lemma T of `covering-towers-iff-effective-minimal-free-subshifts-proof`:
  - If the returns of `P_n` contain a subgroup `H_n` with `B(R_n)H_n = Λ`, then
    `y` is `H_n`-periodic.
  - So subgroup-skeleton or Toeplitz designs cannot give (OC).
  - Over infinite simple groups, finite-index skeletons do not exist anyway, and
    no alternative source of margin returns is known here.
- *Belief.* (OC) is a rigid, "Pisot-like" condition. It is a useful sufficient
  target for groups with rotation-like (cut-and-project) models. Over non-MAP
  groups there is no compact internal space to project from.
  - A homomorphism of an infinite simple `Λ` into a compact group with infinite
    image is injective, so `Λ` would be MAP.
  - Finitely generated MAP groups are residually finite (Malcev, context only).
  - Hence no such model exists for these inputs, and the claim may fail for simple
  Kazhdan inputs while (M2) holds.

## Attempts

None beyond the evidence above.
