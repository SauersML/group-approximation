---
rg: 2
id: machine-halting-is-one-word-equation
kind: claim
title: Halting of a finite-state Post-Turing machine is a single word equation
artifacts:
  - GroupApproximation/Computability/TM0WordProblem.lean
  - GroupApproximation/Computability/PostMachineHalting.lean
  - GroupApproximation/Computability/PostMachineTM0.lean
  - GroupApproximation/Computability/PostMachine.lean
  - GroupApproximation/Computability/StringRewriting.lean
  - GroupApproximation/Computability/RewriteSimulation.lean
  - GroupApproximation/Computability/MachineRestrict.lean
  - GroupApproximation/Computability/FiniteMachineWordProblem.lean
---

ESTABLISHED, unconditionally, for an arbitrary machine.
`Computability.TM0WordProblem.tm0_eval_dom_iff_mk_eq_finalWord`: for a
`Turing.TM0` machine `M` there is an explicit finite list of rewriting rules
`R` -- `RewriteSystem` is a `List (List a x List a)`, so finiteness is
structural, not asserted -- and one fixed four-letter word `finalWord`, with

    (TM0.eval M l).Dom  <->  mk R (encode (liftCfg (ofInput l))) = mk R finalWord.

Halting is thereby *one equation* in the presented monoid, between the word
encoding the initial configuration and a word that does not depend on the
input.

Two chains meet at that statement.  `PostMachineHalting` ends at
`haltingSystem_mk_eq_finalWord_iff`: for the listed rules, the equation holds
exactly when the machine halts from the given configuration.  `PostMachineTM0`
ends at `eval_dom_iff`: the machine of `Computability.PostMachine` halts from
an input list exactly when Mathlib's `TM0.eval` on the same list terminates.

## The finiteness side condition, and where it is discharged

`FiniteMachineWordProblem.not_computablePred_wordProblem_of_finite` is the
form the consumer wants: given undecidable halting on a family of inputs,
*and* a `Finset` of states containing `default` and closed under transitions,
the word problem of the resulting finite system is not computable.  The
side condition is exactly Mathlib's `TM0.Supports`.  `MachineRestrict`
performs the restriction to those states and proves nothing is lost.

Nothing in this claim is specific to any machine; it is the transport of
halting into a word problem, and it is why any theorem producing an
undecidable `TM0.eval` hands its undecidability straight to a monoid.
