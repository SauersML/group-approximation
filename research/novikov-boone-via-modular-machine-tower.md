---
rg: 2
id: novikov-boone-via-modular-machine-tower
kind: route
title: Apply the halting biconditional to a machine with non-computable halting set
target: novikov-boone-fp-group-undecidable-word-problem
requires: [boone-commutator-criterion-for-halting, boone-final-group-finitely-presented, modular-machine-with-noncomputable-halting]
artifacts:
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
  - GroupApproximation/Computability/BooneGroupBase.lean
---

## Why sufficient

The three prerequisites are, in order, the mathematics, the adjective, and the
computational input, and the composition is two lines.

Take the machine `M` supplied by the third prerequisite.  The first gives, for
every `(a,b)`,

    [k, t(a,b)] = 1  in  (G'_M)'   <->   M.Halts (a,b),

so a decision procedure for the word problem of `(G'_M)'` would decide `H_M`;
the map `(a,b) |-> [k, t(a,b)]` is computable as a word in the generators, so
`ComputablePred.of_eq` -- or the reductions of
`Mathlib/Computability/Reduce.lean` -- transports non-computability from `H_M`
to the word problem.  The second prerequisite is what makes the resulting group
*finitely presented*, which is the adjective the claim asserts and the only
thing it is used for.

## Why the split is at exactly these three places

The first prerequisite is the entire mathematical content of Novikov--Boone and
is stated for an arbitrary modular machine, with no undecidability in it; this
is deliberate, so that no repository theorem can depend on the unproved
Theorem 4 through it.  The third is that theorem, stated nowhere in Lean.  The
second is orthogonal to both: it is about presentations, not about halting, and
its failure would leave the biconditional intact while making the conclusion
unstatable.
