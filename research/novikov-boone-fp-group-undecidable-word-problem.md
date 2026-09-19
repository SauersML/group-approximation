---
rg: 2
id: novikov-boone-fp-group-undecidable-word-problem
kind: claim
title: A finitely presented group with undecidable word problem
distinct_from:
  markov-post-undecidable-monoid-word-problem: That is the MONOID statement, established here unconditionally; this is the group statement, which the modular-machine route reaches without using it -- the two are independent, and closing D3 does not shrink D4.
  adian-rabin-transform-for-mf: That is the effective transformation on presentations with a triviality-versus-containment dichotomy; this is only the undecidable source group it consumes, item D4 of that claim's cost table.
  literal-word-problem-solvable: That records that the manuscript's own group E has SOLVABLE word problem, by an explicit algorithm; this asks for a different, purpose-built group where the word problem fails to be decidable.
  torsion-free-finitely-presented-non-mf: That asks for a finitely presented group failing an approximation property, with no decision problem in it; this asks for one whose word problem is undecidable, and says nothing about MF or torsion.
artifacts:
  - GroupApproximation/Computability/NovikovBoone.lean
  - GroupApproximation/Computability/BooneWordProblem.lean
  - GroupApproximation/Computability/BooneGroupFinitePresentation.lean
  - GroupApproximation/Computability/ModularMachineUndecidable.lean
  - GroupApproximation/Computability/BooneGroupBase.lean
  - GroupApproximation/Computability/BooneGroupTower.lean
---

ESTABLISHED (2026-08-16),
`Computability/NovikovBoone.exists_finitelyPresented_wordProblem_not_computablePred`:
there is a finitely presented group and a sequence of words in it for which
triviality is not decidable.  Unconditional, with no literature input --- the
only undecidable source anywhere in the chain is Mathlib's
`ComputablePred.halting_problem`.

Item **D4** of the cost table in [[adian-rabin-transform-for-mf]], and its
critical path.  To the best of current knowledge this had never been done in
any proof assistant.

## Where the chain stands

Seven modules are in place, and the roadmap in `Computability/BooneGroupBase`
tracks them stage by stage.  Established, and all machine-checked:

* [[modular-machine-halting-invariance]] (S0) -- the three machine facts;
* [[free-subbasis-subgroup-calculus]] (S1) -- sub-basis subgroups of a free
  group;
* [[boone-base-group-and-lemma-five]] (S2, S2b) -- the base group and Lemma 5;
* [[boone-base-group-two-generator-one-relator]] (S2c) -- the presentation;
* [[boone-hnn-tower-embeds-base-group]] (S3) -- the tower, one stable letter at
  a time, with its embedding invariant;
* [[boone-halting-index-good-parameter-set]] (S5a) -- the base-group half of
  both good-subgroup verifications;
* [[hnn-good-subgroup-lemma]] (S4) -- the only item that carried mathematical
  rather than bookkeeping risk, closed on 2026-08-16 with no induction on
  stable letters, together with its iteration up the tower;
* [[boone-tower-good-subgroup-transport]] (S5b) -- goodness of the halting
  subgroup at every quadruple, in both directions, with `GoodTower` discharged
  for an actual machine;
* [[boone-halting-subgroup-is-normal-closure]] (S6) -- Simpson's Lemma 7, the
  lift of the halting subgroup is the lift of `⟨t⟩`;
* [[boone-commutator-criterion-for-halting]] (S7) -- **the target statement**:
  in `G_M`, `k` commutes with `t(α,β)` exactly when `(α,β)` halts, for an
  arbitrary modular machine.

* [[boone-final-group-finitely-presented]] (S8) -- `G_M` is finitely presented,
  for every modular machine, on the strength of
  [[hnn-extension-finite-presentation-permanence]] and
  [[boone-normal-closure-of-t-finitely-generated]].

* [[modular-machine-with-noncomputable-halting]] (S9) -- Simpson's Theorem 4,
  the last external input, closed by reading a modular machine as a two-stack
  machine and simulating a Post-Turing tape with it.

Nothing is open.  The capstone is `Computability/NovikovBoone`, which is the
conjunction of S7's biconditional, S8's finite presentation and S9's machine,
all three about the same group `G_M`.

**Novikov--Boone is therefore complete.**  S3--S7 produce the halting
biconditional for an arbitrary modular machine, S8 makes that group finitely
presented, and S9 supplies a machine whose halting set is not computable; the
capstone composes them along the computable map `(a,b) |-> [k, t(a,b)]`.  Every
stage is machine-checked, and the chain contains no literature input at any
point.

## Why this route

Not Boone 1954--57 as streamlined by Britton (Lyndon--Schupp IV.7, Rotman
Ch. 12), whose four-stage tower over a free group has associated subgroups
given by a long list of words and whose correctness is a multi-page case
analysis.  The chain follows Aanderaa--Cohen modular machines in Simpson's
written-out form: one base group, one family of stable letters all of the same
shape, one further letter, and correctness in three short lemmas.  Mathlib's
`HNNExtension`, its normal form and Britton's Lemma are genuine enablers and
are what make the estimate this small.
