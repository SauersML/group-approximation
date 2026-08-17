---
rg: 2
id: markov-post-from-finite-state-support
kind: route
title: Feed the undecidable machine into the word encoding, with Mathlib's support chain supplying finiteness
target: markov-post-undecidable-monoid-word-problem
requires: [undecidable-post-turing-machine, machine-halting-is-one-word-equation]
artifacts:
  - GroupApproximation/Computability/MarkovPost.lean
---

## Why sufficient

The two prerequisites are the two halves and neither mentions the other: one
produces a machine with undecidable halting, the other turns halting of an
arbitrary *finite-state* machine into one equation in a finitely presented
monoid.  What the composition needs, and what is neither prerequisite, is the
finiteness side condition -- a `Finset` of states containing `default` and
closed under transitions -- for the particular machine the first prerequisite
produces.  Supplying it is the content of this route.

## Discharging the side condition

`MarkovPost.exists_undecidable_wordProblem` runs Mathlib's own support chain
on the machine `M0 = TM1to0.tr (TM2to1.tr tr)`:

    tr_supports c Cont'.halt          : TM2.Supports tr (codeSupp c Cont'.halt)
    TM2to1.tr_supports                : TM1.Supports ...
    TM1to0.tr_supports                : TM0.Supports M0 (trStmts ...)

and the conclusion's carrier is a `Finset`.  Its two components are then
translated into the shape `not_computablePred_wordProblem_of_finite` asks for:
`hs0.1` is `default in S0` verbatim, and closure is `hs0.2` after unfolding
`ofTM0` and case-splitting on whether `M0 q a` is `none` or `some`.

Two instances have to be supplied by hand, which is the only reason this is
not a one-liner: `Fintype` for `PartrecToTM2.K'` (Mathlib derives
`DecidableEq` and `Inhabited` but not `Fintype`, and the tape alphabet's
finiteness needs it) and `Fintype (TM2to1.G' K' _)`, since `TM2to1.G'` is a
`def` and instance search does not unfold it.

The input family is `fun m => TM2to1.trInit K'.main (trList [m])`, matching
the family on which the first prerequisite's undecidability is stated.

## Not a restatement of either prerequisite

The first prerequisite is about `TM0.eval` and says nothing about words; the
second is about words and says nothing about which machine, and is vacuous
without a machine whose halting is undecidable *and* whose visited states are
finite.  The route is where those two facts about one and the same machine are
made to hold simultaneously.
