---
rg: 2
id: markov-post-undecidable-monoid-word-problem
kind: claim
title: A finitely presented monoid with undecidable word problem
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: That asks for a finitely presented GROUP, which is strictly harder and which the modular-machine route reaches without passing through this statement; this is the monoid (semi-Thue) statement, and it is established.
  adian-rabin-transform-for-mf: That is a computable transformation between presentations with a triviality-versus-containment dichotomy; this is only the undecidable source at the monoid level, item D3 of that claim's cost table.
  operator-mf-is-a-markov-property: That is a statement about groups and an approximation property, saying MF is inherited, forbidden and nontrivially witnessed; this is about monoids and rewriting, and has no MF in it at all.
artifacts:
  - GroupApproximation/Computability/MarkovPost.lean
  - GroupApproximation/Computability/FiniteMachineWordProblem.lean
  - GroupApproximation/Computability/UniversalMachineUndecidable.lean
  - GroupApproximation/Computability/TM0WordProblem.lean
---

ESTABLISHED, unconditionally and with no literature input.
`Computability.MarkovPost.exists_undecidable_wordProblem`: there are finite
alphabets and a finite rewriting system `R` over them, together with a family
of words `g : N -> List (Letter G0 (HState L0))`, such that

    not ComputablePred (fun m => mk R (g m) = mk R finalWord).

Equality is in the monoid presented by `R`; `RewriteSystem` is a `List` of
rules, so "finitely presented" is structural.  This is **Markov--Post**, and
it closes item **D3** of the cost table in [[adian-rabin-transform-for-mf]].

## The obstacle that turned out not to be one

The chain needs a machine with *finitely many* states, because a finite
alphabet of letters is what makes the rule list finite; and the state type of
Mathlib's translated machine, `PartrecToTM2.L'`, is infinite -- its states
carry continuations, which carry codes.  An earlier reading of this chain
recorded finiteness of the visited state set as the remaining obstacle.

It was already in Mathlib, one namespace away from the theorems that build the
machine: `PartrecToTM2.tr_supports` on the finite set `codeSupp c k`, then
`TM2to1.tr_supports`, then `TM1to0.tr_supports`, whose conclusion is
`TM0.Supports (tr M) (trStmts M S)` with `trStmts M S` a `Finset`.
`TM0.Supports` unfolds to `default in S` together with closure of `S` under
transitions, which is exactly the hypothesis
`not_computablePred_wordProblem_of_finite` asks for.  Two `deriving`/`letI`
lines were the whole remaining gap: Mathlib derives `DecidableEq` and
`Inhabited` for the four-stack index type `K'` but not `Fintype`, and
`TM2to1.G'` is a `def`, so instance search does not see through it.

## Noncomputability, which does not weaken the statement

The construction is noncomputable: the TM0 state type is
`Option (TM1.Stmt G L s) x s` and `TM1.Stmt` contains function types, so it
has no decidable equality, and the restriction to a `Finset` of states decides
membership classically.  What is asserted is that the monoid is presented by a
finite list of rules and that *its word problem* is undecidable; finding the
presentation effectively is not part of the claim and is not needed by any
consumer.

## What this does not give

It does not give a finitely presented **group** with undecidable word problem.
Nothing in the group chain consumes it either: the modular-machine route of
[[novikov-boone-fp-group-undecidable-word-problem]] takes its computational
input from [[modular-machine-with-noncomputable-halting]], not from a monoid
statement.  So D3 and D4 are independent, and D3 being closed does not shrink
D4.

An earlier, separate reduction lives in
`Computability/SemigroupWordProblem*` (four modules): a deterministic Turing
machine, its semi-Thue system, and a two-directional simulation, whose
docstrings state that the universal-machine half was missing.  That half is
what the modules cited above supply, by a different encoding.
