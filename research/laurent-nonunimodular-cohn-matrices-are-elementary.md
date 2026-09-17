---
rg: 2
id: laurent-nonunimodular-cohn-matrices-are-elementary
kind: claim
title: "Cohn matrices at primitive non-unimodular vectors over Z[t,t^-1] are elementary"
distinct_from:
  sl2-laurent-elementary-subgroup-is-normal: that concerns Cohn matrices at unimodular vectors (the conjugates of E_12(1)); this concerns the primitive vectors generating a proper ideal, which no conjugation relates to E_12(1).
artifacts:
  - experiments/sl2-laurent-e2-census-2026-09-17/mreduce.py
  - experiments/sl2-laurent-e2-census-2026-09-17/level_census.py
  - experiments/sl2-laurent-e2-census-2026-09-17/mcensus.py
  - experiments/sl2-laurent-e2-census-2026-09-17/hard_cases.py
  - experiments/sl2-laurent-e2-census-2026-09-17/results.txt
  - experiments/sl2-laurent-e2-census-2026-09-17/wide_cases.py
  - experiments/sl2-laurent-e2-census-2026-09-17/vorbit.py
  - experiments/sl2-laurent-e2-census-2026-09-17/vreduce.py
  - experiments/sl2-laurent-e2-census-2026-09-17/vreduce_results.txt
---

Let `R = Z[t,t^{-1}]`. Suppose `p, q ∈ R` have no common non-unit factor and
`pR + qR ≠ R`. Then

`C(p,q) = [[1+pq, p^2],[-q^2, 1-pq]]`

is a product of elementary matrices over `R`.

This is condition (C) of the three-way split
`sl2-laurent-elementary-iff-three-unipotent-conditions` of
`sl2-laurent-integers-equals-elementary-subgroup`, and it is necessary for that claim.
Over `Z[t]` and `k[x,y]` the analogous statement is false: Cohn (1966) shows
`C(2,t) ∉ E_2(Z[t])` and `C(x,y) ∉ E_2(k[x,y])`, both at primitive non-unimodular
vectors. Over `R`, `C(2,t)` is no longer of this type, since `t` is a unit.

The condition needs one matrix per `E_2(R)`-orbit of vectors
(`sl2-laurent-elementary-iff-three-unipotent-conditions`, item 5). The basic family
is `C(n,f)` with `n ≥ 2`, `gcd(n, content f) = 1` and `f mod n` not a unit of
`(Z/n)[t,t^{-1}]`. Its class depends only on `f mod n`.

## Attempts

- **Level-2 and level-3 census.** Heuristic search with
  `experiments/sl2-laurent-e2-census-2026-09-17/mreduce.py`: full-matrix best-first
  search over monomial row and column operations, which succeeds once an entry is
  `±t^k`. `level_census.py` runs `C(n,f)` for `f` with coefficients in `[0,n-1]`,
  nonzero ends and positive width. All of these vectors are primitive and
  non-unimodular. Raw outputs are in `results.txt`.
  - At budget 3000: `n = 2`, widths 1 to 5, 14 of 31 reduce; `n = 3`, widths 1 to 3,
    12 of 52 reduce.
  - Reruns with larger budgets (`hard_cases.py`) reduce:
    - `C(2, 1+t+t^3)` in 24660 steps;
    - `C(2, 1+t^2+t^3+t^4)` in 63378 steps;
    - `C(2, 1+t+t^2+t^3+t^4+t^5)` in 22789 steps;
    - `C(3, 1+t+t^2)` in 64269 steps.

  So the failures at budget 3000 are largely search artifacts. The most resistant
  cases found are `C(3, 1+t+2t^2)` (first row `(4+3t+6t^2, 9)`) and
  `C(3, 1+2t+2t^2)`. In both, `f mod 3` is an irreducible quadratic over `F_3`, so
  `R/(3,f) ≅ F_9`. Both fail at budget 150000 under slacks `(3,80)` and `(4,40)`.
  Under slacks `(1,30)`, `(2,40)` and `(2,80)`, the whole pruned search space is
  exhausted (for `C(3, 1+t+2t^2)`: 1961, 24656 and 47576 states). This makes them
  candidates for an invariant, but is not evidence of non-elementarity. Irreducibility
  of `f mod n` alone is not the obstruction: `C(2, 1+t+t^2)` and `C(2, 1+t+t^3)`
  reduce.
- **Mechanism of quick reductions.** In the found paths, one or two column operations
  create a unit entry. For `C(2,f)` this happens when `1 + 4u`, for a unit `u`, has a
  factor congruent to `1 + 2f mod 4`. The Sophie Germain identity
  `1 + 4t^4 = (1+2t+2t^2)(1-2t+2t^2)` explains `f = t + t^2` and `f = 1 + t + t^2`.
  No uniform family of unit-producing identities has been found for all `f`.
- **Where Cohn's degree argument dies.** Cohn's proof over `Z[t]` tracks leading
  degrees of rows under polynomial elementary operations. Over `R`, monomial
  multipliers `m t^k` with `k < 0` cancel lowest terms as well; see the first attempt
  in `sl2-laurent-integers-equals-elementary-subgroup`. So a leading-degree invariant
  is not preserved, and an obstruction to (C) would need an invariant that controls
  both ends at once. The reductions of `C(2, 1+t+t^3)` and `C(3, 1+t+t^2)` were found
  with width slack 2: the summed entry width may exceed its starting value by up to 2.
  It is not known whether width-nonincreasing paths exist for them.
- **Linear census at levels 4 to 7: an apparent pattern that breaks.**
  `level_census.py n 1` runs `C(n, a+bt)`; raw outputs are in `results.txt`.
  - `n = 5` (budget 20000): exactly the 4 matrices with `a, b ≡ ±1 mod 5` reduce,
    in 8 to 12 steps.
  - `n = 7` (budget 3000): exactly the 4 with `a, b ≡ ±1 mod 7` reduce.
  - `n = 4, 6`: the census also includes unimodular and non-primitive `f`.

  The suggested rule, "linear level-n Cohn matrices reduce iff their coefficients are
  ±1 mod n", does **not** hold as a search phenomenon.
  - `C(6, 3+t)` (ideal `(2, 1+t)`) and `C(6, 2+t)` (ideal `(3, t-1)`) fail at budget
    3000. At budget 100000 (`hard_cases.py`), the width-slack-2 pruned spaces are
    exhausted (41636 and 28004 states). The first width-slack-3 runs then reduce
    them at 41639 and 28011 states, only 3 and 7 states later.
  - So these failures come from the width bound, not from the coefficients.
  - `C(5, 2+t)` still fails:
    - at budget 100000 under slacks `(3,80)` and `(4,40)`;
    - at budget 250000 under `(3,300)`, `(5,300)` and `(8,400)` (`wide_cases.py`).
  - `C(5, 2+2t)` exhausts its `(3,80)` space at 57512 states and fails at 100000
    under `(4,40)`.
  - `C(5, 1+2t)` fails at 100000 under all four slacks with width slack at least 2.

  These are the most resistant linear cases, but the level-6 behaviour warns that
  exhausting a width-bounded space is weak evidence.
- **Vector-orbit determinant (proved here).** It limits transport by item 5 of the
  split.
  - Let `p, q ∈ R` be coprime non-units with `I = pR + qR ≠ R`. Since `R` is a UFD,
    `p, q` is a regular sequence, so `I/I^2` is free over `R/I` on the classes of
    `p, q` (standard for ideals generated by regular sequences). A column `w` with
    entries in `I` therefore has a well-defined matrix `M(w)` over `R/I`, given by
    `w_i ≡ α_i p + β_i q mod I^2`.
  - For `Y ∈ SL_2(R)`, `M(Yw) = (Y mod I) M(w)`. So `det M(w) ∈ (R/I)^*` is constant on
    the `SL_2(R)`-orbit of `w`, and all vectors in the orbit generate `I`.
  - For `v_b = (n, -b(t-c))` with `gcd(b, n) = 1` and `c` a unit mod `n`, take
    `I = (n, t-c)`. Then `R/I = Z/n` and `det M(v_b) = -b`. Since `C(-v) = C(v)` and
    `det M(-v) = det M(v)`, the vectors `v_b` for different `b mod n` lie in different
    `SL_2(R)`-orbits.
  - So Lemma 3 / item 5 cannot move a reduction of `C(n, t-c)` to `C(n, 2(t-c))`. The
    level-5 data at `c = -1`: `b = ±1` reduce and `b = ±2` resist, and these lie in
    different orbits.
  - The invariant does **not** predict resistance. For `C(6, 3+t)`, `R/I = F_2` and
    the determinant is trivial, the same as for `C(2, 1+t)`. Yet `C(6, 3+t)` reduces
    only at width slack 3.
  - `vorbit.py` found no `E_2`-path from `(6, -(3+t))` to `±(2, -(1+t))` at budget
    100000 with slack 2 or 3. That is evidence only; finer orbit invariants (mod
    `I^3`, or through the `t ↦ -1` specialization, where both go to `gcd` 2) have not
    been worked out.
- **Mcensus failures rechecked by vector search.** `vreduce.py` searches the
  `E_2`-orbit of the vector `(p, -q)`. A unit coordinate certifies that `C(p,q)` is
  elementary (Lemma 3 of the proof node).
  - Of the 276 budget-1500 `mcensus.py` failures, 40 are certified elementary this
    way, so they were search artifacts (`vreduce_results.txt`).
  - The other 236 reach vectors with a constant coordinate (levels 5, 7, 8, 10, 11,
    ...) without a unit. No vector whose coordinates generate a proper ideal can ever
    reach a unit coordinate. Which of the 236 are unimodular has not been separated
    out.
