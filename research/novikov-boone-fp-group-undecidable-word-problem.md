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
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
  - GroupApproximation/Computability/BooneGroupBase.lean
  - GroupApproximation/Computability/BooneGroupTower.lean
---

OPEN.  Item **D4** of the cost table in [[adian-rabin-transform-for-mf]], and
the critical path of that claim: there is a finitely presented group whose word
problem is not computable.

To the best of current knowledge this has never been done in any proof
assistant.

## Where the chain stands

Seven modules are in place, and the roadmap in `Computability/BooneGroupBase`
tracks them stage by stage.  Established:

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
  subgroup at every quadruple, in both directions.

Open: [[boone-halting-subgroup-is-normal-closure]] (S6, whose inductive step is
proved),
[[boone-commutator-criterion-for-halting]] (S7, the target statement),
[[boone-final-group-finitely-presented]] (S8) and
[[modular-machine-with-noncomputable-halting]] (S9, external and prose-only).

With S4 and S5b closed the estimate drops sharply: S8 is now the one
load-bearing item left, and S6 and S7 are inductions whose steps are in hand.

## Why this route

Not Boone 1954--57 as streamlined by Britton (Lyndon--Schupp IV.7, Rotman
Ch. 12), whose four-stage tower over a free group has associated subgroups
given by a long list of words and whose correctness is a multi-page case
analysis.  The chain follows Aanderaa--Cohen modular machines in Simpson's
written-out form: one base group, one family of stable letters all of the same
shape, one further letter, and correctness in three short lemmas.  Mathlib's
`HNNExtension`, its normal form and Britton's Lemma are genuine enablers and
are what make the estimate this small.
