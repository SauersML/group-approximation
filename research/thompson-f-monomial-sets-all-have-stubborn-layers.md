---
rg: 2
id: thompson-f-monomial-sets-all-have-stubborn-layers
kind: claim
title: Every finite monomial set of the positive monoid of F with at least two elements has a stubborn layer, so no private pivot order exists for any of them and the triangular doubling certificate has no instance in F
distinct_from:
  thompson-f-staircase-sets-have-stubborn-layers: that is the quantitative law 2a+1 = 3^(d-1)(2m+1) for the staircase family only; this is the qualitative statement for every finite S, and the census here shows the law's divisibility is NOT an invariant of general sets.
  thompson-f-p22-monomials-admit-no-private-pivot-order: that settles the single set S_(3,5) and gives the peeling characterization; this conjectures the same for every finite S.
  thompson-f-generator-sets-admit-no-private-pivot-order: that is the proved degree-one case; this is the statement for all degrees.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that is the doubling criterion for non-amenability; this kills one sufficient certificate for doubling and says nothing about doubling itself.
artifacts:
  - experiments/thompson-f-pivot-orders-2026-09-18/README.md
  - experiments/thompson-f-pivot-orders-2026-09-18/small_set_census.py
  - experiments/thompson-f-pivot-orders-2026-09-18/small_set_census_letters2.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/small_set_census_letters3.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/small_set_census_deg3.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/prefix_core.cpp
  - experiments/thompson-f-pivot-orders-2026-09-18/verify.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/survivors.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/family.jsonl
  - experiments/thompson-f-pivot-orders-2026-09-18/law_test.jsonl
---

**OPEN.** Notation as in `thompson-f-stubborn-sets-split-off-the-tail`: `M` is the positive monoid of
Thompson's `F` as a monoid of forests, `S ⊆ M_d` is a finite set of normal forms of one degree,
`P_a(S)` is the prefix world of forests with `K(S)` roots and `a` carets, and `core(P_a)` is its
largest stubborn subset. A stubborn subset of any layer kills every private pivot order for `S`
(`thompson-f-p22-monomials-admit-no-private-pivot-order`, item 1), hence every *triangular* doubling
certificate that `thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs` can build from
`S`.

**Conjecture.** For every finite `S ⊆ M_d` with `|S| >= 2` there is an `a` with `core(P_a(S)) ≠ ∅`.
Equivalently: **no finite set of positive monomials of `F` admits a private pivot order.**

(The hypothesis `|S| >= 2` removes only a degenerate case, not a counterexample: for `|S| = 1` the
single successor of every point is private, so `P_0` is already stubborn and `a_min = 0`, and such an
`S` doubles nothing anyway. `|S| >= 4` is in any case forced for a doubling set by item 5 of
`thompson-f-invariant-pivot-orders-cannot-certify-doubling`.)

**Why this is the class kill.** The pivot-order certificate is the order-based route to the
doubling criterion `thompson-f-nonamenable-iff-some-monomial-set-doubles`. If the conjecture holds,
that route has no instance anywhere in `F`, and a doubling proof must be *non-triangular*: a Hall-type
2-to-1 matching not induced by any total order, or a flow. The invariant that kills every member is
the stubborn set, and the step where each dies is the same: under any total order the minimum of a
stubborn set has at most one private point.

**Evidence.**
1. *Proved for degree one.* Every `X_m = {x_0, ..., x_m}` has a stubborn layer, by the explicit
   two-block construction of `thompson-f-generator-sets-admit-no-private-pivot-order`, and no layer
   below `D = m` has one (`thompson-f-stubborn-sets-split-off-the-tail`, item 3).
2. *Exhaustive small census* (`small_set_census.py`). Every subset of size `>= 2` of the six degree-2
   monomials with letters `<= 2` — all **57** of them — has a stubborn layer, with
   `a_min ∈ {1, ..., 10}` (`small_set_census_letters2.jsonl`; the distribution is
   `a_min = 4` for 19 sets, `2` for 11, `1` for 7, `6` for 6, and single digits elsewhere). Six
   sampled degree-3 sets likewise, `a_min <= 7` (`small_set_census_deg3.jsonl`). The same search was
   run over the subsets of size `>= 2` of the ten degree-2 monomials with letters `<= 3`
   (`small_set_census_letters3.jsonl`) with a budget of `|P_a| <= 2 · 10^6`, which lets every one of
   them be searched through layer `a = 10` exactly. It covers **961** sets: every subset of size 2
   (45), 3 (120), 4 (210), 5 (252), 6 (210) and 7 (120), and 4 of size 8; the run was stopped there.
   Of these, 572 have a computed `a_min <= 10` and the rest have `a_min > 10`. **No set was found
   that survives.** The sets with `a_min > 10` are the larger ones, for which the law of
   `thompson-f-staircase-sets-have-stubborn-layers` puts `a_min` past the budget anyway — its own
   members have `a_min = 7` at `S(2,2)` (9 monomials), 10 at `S(3,2)` (14) and 13 at `S(4,2)` (20).
3. *The named sets.* `S_(2,4)` at 4, `S_(3,5)` at 7, `S_(4,6)` at 10, `{x_0^2, x_1^2, x_2^2}` at 4,
   `X_0X_1X_2` at 4, `X_1X_2X_3` at 13, `X_0..X_3` at 13.
4. *The two sets the graph lists as surviving are only shallow.* `thompson-f-is-not-amenable` records
   `S(2,3) = {x_a x_b x_c : a <= 2, b <= 3, c <= 4}` as having no stubborn layer; the census now
   reaches `a = 12` (17 298 645 points) and `thompson-f-staircase-sets-have-stubborn-layers` predicts
   `a_min = 22`. The same holds for the 21 degree-2 monomials with letters `<= 5`, now empty through
   `a = 11`. A long empty prefix of the layer sequence is exactly what the staircase family produces
   by design.
5. *No shortcut through arithmetic.* The divisibility `2 a_min + 1 ≡ 0 (mod 3^(d-1))` that holds on
   the staircase family is **not** an invariant of general monomial sets: of the 57 exhaustively
   resolved degree-2 sets with letters `<= 2`, **26 violate it** (for example `{x_0^2, x_1^2}` has
   `a_min = 2`, so `2a+1 = 5`); in the letters-`<= 3` census 312 of the 572 resolved sets violate it;
   and all six sampled degree-3 sets violate it. So a proof cannot go through a congruence; it needs
   a construction for each `S`.

**Calibration: this is not evidence for amenability.** A stubborn set does not contradict doubling.
`S_(3,5)` has a 1092-point stubborn set at degree 7 while its layer expansion there is
`Λ ≈ 3.07 > 2`, so the very same set may well double; what fails is only the order-based *proof* of
doubling. Symmetrically, the empty layers below `a_min` give `Λ_S(D) >= 2` for `D < a_min`, i.e. `S`
doubles every finite subset of those layers (item 3 of
`thompson-f-p22-monomials-admit-no-private-pivot-order` inside the window, moved to the whole layer
by item 1 of `thompson-f-monomial-doubling-ratio-is-a-finite-computation`; recorded as item 4 of
`thompson-f-stubborn-sets-split-off-the-tail`, which is a re-derivation of that bound and not a
stronger certificate), and the staircase family makes such windows arbitrarily long. Neither side of the computation moves
`thompson-f-is-amenable` or `thompson-f-is-not-amenable`.

**Falsifiable first step.** Exhibit one finite `S` with `|S| >= 2` and `core(P_a) = ∅` for every `a`,
or prove `core(P_a) = ∅` for all `a` for one candidate — that would prove `F` non-amenable through
`thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs`, so it is not a cheap step. The
cheap direction is the other one: a construction of a stubborn set for a general `S`, of which the
only known instance is the two-block set for degree one, and whose next case is the staircase law
(`thompson-f-staircase-sets-have-stubborn-layers`, need 7a3ee718 on the bus).

## Attempts

- **A congruence shortcut (2026-09-18).** The staircase law reads `2a_min + 1 = 3^(d-1)(2m+1)`, and a
  binary tree with `a` carets has `2a+1` nodes, so one might hope `2 a_min(S) + 1` is a `3`-adic
  invariant of `S` for every degree-`d` set. Dies immediately off the staircase family: 26 of the 57
  degree-2 sets with letters `<= 2` have `2a_min + 1` not divisible by 3. The invariant is not
  arithmetic.
- **Counting (2026-09-18).** Item 3 of `thompson-f-p22-monomials-admit-no-private-pivot-order` gives a
  stubborn set from any `Y` with `|S Y| < 2|Y|`, so a doubling *failure* would settle a set at once.
  Dies for the interesting sets: `Λ_(S_(3,5))(D) >= 2` through `D = 12`
  (`thompson-f-monomial-doubling-ratio-is-a-finite-computation`), and the stubborn set at `D = 7`
  lives where `Λ ≈ 3.07`. Stubbornness is strictly finer than non-doubling, so no counting argument
  can reach it.
