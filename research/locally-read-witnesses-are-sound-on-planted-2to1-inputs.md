---
rg: 2
id: locally-read-witnesses-are-sound-on-planted-2to1-inputs
kind: claim
title: On the proved Grassmann 2-to-1 instances, any witness map from right-hand sides to orientation-lift labellings has average value on planted YES inputs at most the soundness plus the mass of constraints whose read set refutes a sound NO right-hand side, for every orientation and with no efficiency assumption
distinct_from:
  view-local-branch-selectors-are-gauge-blind: that randomises the gauge z and bounds honest labellings t+z of equivariant menus under parity-faithful selectors, getting one half; this couples planted YES inputs with a NO coset, bounds arbitrary labellings produced from the right-hand sides (not honest ones), allows any selector, and gets the soundness eta rather than one half.
  high-advantage-selector-witnesses-decode-good-outer-labellings: that decodes near-honest witnesses of high lift value into outer labellings; this needs no decoding and no structure of the witness, only which right-hand sides its acceptance events read.
  dkkms-grassmann-2to1-test-is-locally-99-percent-rigid: that is a structure theorem for all near-1 labellings; this is an information bound for labellings given as functions of the right-hand sides, and it holds whether or not rigidity does.
  efficient-branch-selector-on-proved-2to1-instances: that is the open selector hole; this proves a necessary condition on any YES witness for it, without closing it.
  view-local-selectors-beat-one-half-through-non-honest-witnesses: that asks whether non-honest witnesses beat one half for view-local selectors; this caps every non-honest witness map whose read sets do not refute sound NO right-hand sides at eta, for every selector.
artifacts:
  - experiments/ugc-local-witness-2026-09-17/check_local_witness_coupling.py
---

**ESTABLISHED.** Route: `locally-read-witnesses-planted-coupling-proof`. The proof
is elementary linear algebra plus two imported facts: the soundness of the
reduction `R_eta` (from `two-to-two-games-theorem`, as used in
`efficient-branch-selector-on-proved-2to1-instances`) and the upper half of the
sandwich (`orientation-lifts-sandwich-2to1-game-values`, item 1). The artifact
checks the exact identity on a toy instance.

## Setting

A regular 3LIN instance is `(H, b)`. `H` has rows `m_1, ..., m_M in F_2^n` of
weight 3, and `b in F_2^M`. For a set `S` of rows, `H_S` is the submatrix and
`Im H_S = {(<m_j, x>)_(j in S) : x in F_2^n}`. `val(H, b)` is the largest
fraction of equations an assignment satisfies.

`G_b := R_eta(H, b)` is the folded DKKMS Grassmann 2-to-1 game (verbatim in
`dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`). Its vertices,
classes, constraints and weights depend on `H` only. `b` enters only through the
folding offsets `h_U(x_e) = b_e`. So there is one weighted constraint set `E(H)`,
and for each `b` a predicate on each `e in E(H)`.

A **witness map** `Lambda` assigns to every `b in F_2^M` an orientation `o(b)` of
`G_b` and a labelling `Lambda(b)` of the lift `U_(o(b))(G_b)`. It need not be
efficient, uniform or honest. The plain case, a labelling of `G_b` itself, is
the special case where the lift bits are ignored.

A **read set** for `Lambda` at `e` is a set `S_e` of rows such that the event
"`e` is accepted in `U_(o(b))(G_b)` by `Lambda(b)`" is a function of `b|S_e`
alone. The trivial read set `S_e = [M]` always works. For `b0 in F_2^M` put

```text
mu_(b0)(Lambda, S) := weight of { e : b0|S_e  notin  Im H_(S_e) }.
```

This is the mass where `b0` is **locally refuted** on the read set. If the rows
of `S_e` are linearly independent, then `Im H_(S_e)` is everything and `e` never
counts.

A right-hand side `b0` is **sound** for `H` if `val(H, b0) <= s*`, where `s*` is
the constant of Theorem 4.1 of DKKMS, quoted in `dkkms-selector-membership-proof`.

## Theorem (planted / NO-coset coupling)

Fix `eta`, a regular `H`, a witness map `Lambda` with read sets `S`, and a sound
`b0`. Let `t` be uniform in `F_2^n`. Then

```text
E_t  val_(U_(o(Ht))(G_(Ht)))( Lambda(Ht) )   <=   eta  +  mu_(b0)(Lambda, S).
```

Every planted input `(H, Ht)` is a YES input of value 1. The bound holds for
every orientation, and it uses no complexity assumption.

*Proof sketch* (full proof in the route).
1. **Translation.** `x -> x + t` is a bijection from the assignments of
   `(H, b0)` to those of `(H, b0 + Ht)` that satisfies the same equations. So
   every `b0 + Ht` is sound, and `R_eta` soundness gives `val(G_(b0+Ht)) <= eta`.
   Forgetting the lift bits keeps every accepted constraint accepted, so every
   labelling of every lift of `G_(b0+Ht)` has value `<= eta`.
2. **Laws.** `t -> H_S t` is linear. So `b|S` is uniform on `Im H_S` when
   `b = Ht`, and uniform on `b0|S + Im H_S` when `b = b0 + Ht`. These two laws
   are equal exactly when `b0|S in Im H_S`.
3. **Per-constraint equality.** On every `e` outside the refuted mass, the
   acceptance event is one fixed function of `b|S_e` whose argument has the
   same law in both cases. So the acceptance probabilities over `t` are equal.
   Sum with weights, bound the refuted mass by 1, and apply step 1 for each `t`.
   QED.

## Corollaries

* **(C1) What a YES witness must read.** Suppose some witness map reaches lift
  value `>= 1 - eta'` on every planted input of `H`, for instance a solution of
  the selector hole together with any choice of YES labellings. Then
  `mu_(b0)(Lambda, S) >= 1 - eta' - eta` for **every** sound `b0`, and for every
  choice of read sets. So on all but `eta + eta'` of the constraint mass, the
  witness's acceptance event must depend on a set of right-hand sides on which
  every sound NO right-hand side is locally unsatisfiable. That is a set
  carrying a parity cycle `sum_(j in T) m_j = 0` with `sum_(j in T) b0_j = 1`.
  The invariant is local satisfiability of the NO coset on read sets.
* **(C2) Fixed rules.** For a fixed `Lambda`,
  `Pr_t[ val(Lambda(Ht)) >= c ] <= (eta + mu_(b0)) / c`. A witness recipe whose
  read sets are rowwise independent outside mass `mu` certifies completeness
  `c` on at most a `(eta + mu)/c` fraction of the planted inputs of `H`.
* **(C3) Tree-like reads.** A set of rows whose incidence hypergraph is a
  hyperforest is linearly independent: some row has a variable of degree 1, so
  peel it off and induct. Consider rules in which, at each constraint, the
  class label, the B-label and the orientation bit read the right-hand sides of
  a bounded-radius neighbourhood of that constraint's tuples, and the predicate
  reads the tuples adjacent to it. On every `H` carrying a sound `b0`, this
  family has average value over planted inputs at most `eta + w_cyc`, where `w_cyc` is the weight of constraints whose total read set
  is not a hyperforest. The gauge-blind node restricts the views of the
  selector and allows only honest witnesses. Here both the selector's bits and
  the witness labels count toward the read set, and the witness need not be
  honest. So the cap is `eta` rather than one half, over a different class.
* **(C4) Need 207b4529 (branch-coordinate germ).** That need asks for class
  labels `sigma_C` with `ker(unfold_U sigma_C) meet L = D(L)` on all but `delta'`
  of the A-mass, where `D(L)` is the dominant seed hyperplane. With `B = 0` and
  the constant orientation, such labels accept exactly the constraints with
  `L' = D(L)`. Their member-level value is at least `share - delta'`, where
  `share = E max_R w(R | U, L)`. The B-labels and the orientation read nothing.
  Let `w_fold` be the weight of folded constraints whose adjacent member tuples
  are not rowwise independent (see the last paragraph). Outside that weight, the
  folded value of these labels is `>= share - delta'`. So by the theorem, any
  map `b -> sigma(b)` realising the need on planted inputs, with exceptional mass
  `delta'(t)`, has class read sets that refute every sound `b0` on at least
  `share - E_t delta'(t) - eta - w_fold` of the mass. The artifact gives
  `share` about 0.50, 0.65, 0.76, 0.83 for `k = 2, 4, 6, 8` (`l = 3`,
  `beta = 1/2`).

  The natural per-class recipe, "take the plurality of the members' forced
  labels", reads the right-hand sides of all member tuples of the class. That
  can be a refuting set only through cycles that close across different member
  tuples. The need is therefore **not** refuted. It is reduced to a global
  statement: the class labels must encode parity cycles of the source across
  member tuples. No choice of `sigma_C` whose read sets leave sound `b0`
  locally satisfiable on more than `1 - share + delta' + eta + w_fold` of the
  mass can realise it.

  *Folded versus member predicates.* Take a folded constraint between `C` (with
  representative `R`, where `R meet H = {0}` by (Q3) of
  `dkkms-selector-membership-proof`) and `(V, L')`, and suppose its adjacent
  member tuples `U', U''` have rowwise independent union. For `z in L'`, the
  decomposition `z = r + y` with `r in R` and `y in H` is unique, and `y` lies in
  `H_(U') meet H_(U'') = H_(U' meet U'')` with the same coefficients. So the
  member extensions agree on `L'`. All member predicates of that folded
  constraint coincide, and folded acceptance equals member acceptance there.
  Without independence, nothing here is claimed.

## Scope

* **Sound NO right-hand sides exist on dense-enough `H`.** Suppose `s* > 1/2`,
  put `eps := s* - 1/2`, and let `M >= n / eps^2`. Fix an assignment `a`. For a
  uniform `b0`, the number of equations `a` satisfies is `Bin(M, 1/2)`, so
  `Pr[ >= s* M ] <= exp(-2 eps^2 M) <= exp(-2n) < 2^(-n)`. A union bound over
  the `2^n` assignments shows that some `b0` has `val(H, b0) <= s*`. If
  `s* = 1/2` exactly, the hypothesis "H carries a sound `b0`" must be checked
  separately. The theorem is stated under that hypothesis.
* **Domain.** `Lambda` is defined on all of `F_2^M`, so that a NO coset input
  has a labelling. A recipe written only for YES inputs is covered as soon as
  its formula makes sense on every `b` with the same read sets. Rules such as
  "a function of `b|S`" or "the plurality of forced labels" are of this kind.
* **Not claimed.** Nothing here bounds witnesses whose read sets contain parity
  cycles refuting `b0`. Examples are the honest labelling `b -> x(b)|R` with
  `x(b)` a solution of `Hx = b`, which reads everything, and labellings built
  from long cycles through member tuples. The selector hole itself stays OPEN.
  Neither UGC nor the Rich 2-to-1 Conjecture is proved or refuted.

## Check

`python3 experiments/ugc-local-witness-2026-09-17/check_local_witness_coupling.py`
(default seed 20260918) uses `n = 9`, `M = 12` (rank 9), `k = 2`, `l = 2`,
`beta = 1/2` and 600 sampled constraints, with member-level predicates. It
enumerates all `2^9` values of `t` exactly.

* (a) `b_U` is exactly uniform for all 17 legitimate tuples, under both YES and
  NO.
* (b) Four random local rules give equal `E_t val` as exact fractions, with 0
  per-constraint mismatches.
* (c) The global control (solve `Hx = b`) gives 1 on YES and 0.6975 on the NO
  coset.
* (d) Adding one neighbouring row gives 0 mismatches.
* (e) For every class label reading a dependent 4-row set: with a NO offset that
  is locally satisfiable there, 0 of 600 constraints mismatch; with a locally
  refuting one, 522 of 600 do.

Part 2 samples the test process (1500 samples) and evaluates the posterior of
the B-side hyperplane by the per-equation generating function
`(1 - beta) + beta (a_i / 3) z`, with weights `1/|Gr(3k - 2r, l - 1)|`.

| `l` | `beta` | `k = 2` | `k = 4` | `k = 6` | `k = 8` |
| --- | --- | --- | --- | --- | --- |
| 3 | 1/2 | 0.50 | 0.65 | 0.76 | 0.83 |
| 3 | 1/4 | 0.32 | 0.39 | 0.46 | 0.52 |
| 4 | 1/2 | 0.30 | 0.68 | 0.80 | 0.87 |

The `l = 3`, `beta = 1/2` row matches the bus lemma
`dkkms-smoothing-leaves-the-branch-coordinate-untested` (0.478 to 0.840).
