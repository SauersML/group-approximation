---
rg: 2
id: locally-read-witnesses-planted-coupling-proof
kind: route
title: Translate a sound NO right-hand side by the planted image, match the laws of every read set on which it is locally satisfiable, and transfer the NO soundness of the reduction to the planted YES inputs constraint by constraint
target: locally-read-witnesses-are-sound-on-planted-2to1-inputs
requires: [two-to-two-games-theorem, orientation-lifts-sandwich-2to1-game-values, dkkms-2to1-instances-satisfy-selector-decoding-hypotheses]
artifacts:
  - experiments/ugc-local-witness-2026-09-17/check_local_witness_coupling.py
---

Notation is as in the target claim.

**Imported inputs.**
* (I1) **Soundness of `R_eta`.** `R_eta` is the reduction behind the 2-to-1 form
  of `two-to-two-games-theorem`, as fixed in
  `efficient-branch-selector-on-proved-2to1-instances`. It maps regular 3LIN
  inputs to `Gap-2-to-1[1 - eta, eta]`. In particular, every regular input with
  `val <= s*` (a NO input of regular `Gap3Lin(1 - eps, s*)`, Theorem 4.1 of
  DKKMS as quoted in `dkkms-selector-membership-proof`) goes to a game of value
  `<= eta`.
* (I2) **Shape.** By the verbatim construction in
  `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`, the following
  depend on `H` alone: legitimate tuples, `X_U`, `H_U`, the vertex sets `A` and
  `B`, the edge process, the classes (Lemma 4.1) and the weights. The
  right-hand side enters only through `h_U(x_e) = b_e`, which is used in the
  unfolding.
* (I3) **Upper sandwich, per labelling.** Take any orientation `o` and any
  labelling of `U_o(G)`. If a constraint `e` is accepted, then its left label
  `a` and right label `(s, bit)` satisfy `p_e(a) = s`. So the labelling of `G`
  obtained by forgetting the bits accepts `e` as well. This is the argument
  behind item 1 of `orientation-lifts-sandwich-2to1-game-values`
  (`val(U_o) <= val(G)`).

**Step 1 (the NO coset is sound).** For any `x`, the map `a -> a + x` is a
bijection from the assignments of `(H, b0)` to those of `(H, b0 + Hx)`. It
satisfies equation `j` of the first input iff it satisfies equation `j` of the
second, because `<m_j, a + x> = <m_j, a> + <m_j, x>`. So `val(H, b0 + Hx) =
val(H, b0) <= s*`, and `H` is still regular. By (I1),
`val(G_(b0+Hx)) <= eta`. By (I3), every labelling of every lift of
`G_(b0+Hx)` has value `<= eta`. Applying this to `Lambda(b0 + Ht)` gives
`val(Lambda(b0 + Ht)) <= eta` for every `t`.

**Step 2 (laws of read sets).** Fix a row set `S`. The map `phi_S(t) = H_S t` is
linear, so for uniform `t` every fibre `phi_S^(-1)(v)`, `v in Im H_S`, is a coset
of `ker phi_S`. They all have the same size. Therefore:
* `(Ht)|S` is uniform on `Im H_S`;
* `(b0 + Ht)|S = b0|S + (Ht)|S` is uniform on `b0|S + Im H_S`.

If `b0|S in Im H_S`, the two cosets coincide, and the laws are equal. If the
rows of `S` are independent, `Im H_S = F_2^S`, so this always holds.

**Step 3 (constraint by constraint).** By (I2), `E(H)` and the weights `w_e` are
the same for every `b`. By the definition of a read set, there is a function
`f_e : F_2^(S_e) -> {0,1}` such that `e` is accepted by `Lambda(b)` in
`U_(o(b))(G_b)` iff `f_e(b|S_e) = 1`. This holds for **every** `b`, since
`Lambda` is defined on all of `F_2^M`. Let `Good` be the set of constraints with
`b0|S_e in Im H_(S_e)`. Then

```text
E_t val(Lambda(Ht))  =  sum_e w_e Pr_t[ f_e((Ht)|S_e) = 1 ]
                    <=  sum_(e in Good) w_e Pr_t[ f_e((b0+Ht)|S_e) = 1 ]  +  mu_(b0)
                    <=  E_t val(Lambda(b0 + Ht))  +  mu_(b0)
                    <=  eta + mu_(b0).
```

The first inequality uses Step 2 on `Good` and bounds each probability outside
`Good` by 1. The last uses Step 1. QED.

**Corollaries.** (C1) is the theorem with the hypothesis `val >= 1 - eta'` on
every planted input, rearranged. (C2) is Markov's inequality applied to
`1 - val` over `t`. (C3) needs one fact, that a hyperforest of rows is
independent. In a nonempty hyperforest some row has a variable that lies in no
other row, so that row is not in the span of the others, and removing it leaves
a hyperforest. (C4) is (C1) applied to the labelling `B = 0`, constant
orientation, class labels `sigma(b)`. It uses the member-predicate coincidence
proved in the target's last paragraph, and it restricts to folded constraints
outside `w_fold`.

**Check.** The artifact computes both sides of Step 3 exactly on a toy
instance, with 600 constraints and all `2^9` values of `t`. It also runs the
control in which `b0` is locally refuted on the read set, where the equality
fails on 522 of 600 constraints.
