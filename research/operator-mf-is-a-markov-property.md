---
rg: 2
id: operator-mf-is-a-markov-property
kind: claim
title: Operator MF is a Markov property of finitely presented groups
distinct_from:
  mf-positive-controls: that records the positive closure facts (subgroups, residually finite, locally finite groups); this assembles two of them plus a negative witness into the specific three-clause package an Adian-Rabin construction consumes, and adds the coding-adequacy clause that turns a statement about groups into a statement about presentation codes.
  kazhdan-clifford-non-mf-construction: that constructs a non-MF group from compression data and a Clifford sign; this is a metamathematical statement about the *class* of MF groups -- isomorphism invariance, one positive member, one forbidden subgroup -- and it uses the existence of a non-MF finitely presented group as a single opaque input, caring about no property of how it was built.
  scaling-family-non-mf: that produces infinitely many non-MF groups by rescaling the construction, and its content is that each member fails MF; this produces no groups at all and asserts instead that the failure of MF is inherited along embeddings and that finite presentations can be coded, which is what an undecidability reduction needs and a family of examples does not supply.
  literal-group-fails-mf-conventions: that asserts the chosen finitely presented group fails MF in every equivalent formulation; this uses that failure once, as the forbidden-subgroup witness, and asserts nothing further about the group.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
  - GroupApproximation/Computability/OperatorMFMarkovWitness.lean
  - GroupApproximation/Computability/PresentationCodes.lean
  - GroupApproximation/Computability/PresentationCodeCompleteness.lean
---

Operator MF satisfies all three clauses of a Markov property of finitely
presented groups:

- **isomorphism invariance** — MF depends only on the isomorphism class;
- **a positive witness** — the trivial group is finitely presented and MF;
- **a forbidden subgroup** — there is a finitely presented group `E` that
  embeds in no finitely presented MF group.

The third clause is the manuscript's own derivation and not an extra
assumption: MF is subgroup-hereditary, so a group failing MF injects into no
group having it, and the chosen finitely presented non-MF group supplies the
failure.

Additionally, the property is a property of **presentation codes** and not
merely of abstract groups: there is a concrete recursive datatype of finite
presentations, `Primcodable`, every one of whose codes names a genuinely
finitely presented group, and **every** finitely presented group is named by
some code.  Adequacy is what stops the statement from being vacuous — a coding
naming only trivial groups would satisfy everything else and support no
reduction at all — and it transfers the two group-level witnesses to
code-level witnesses.

## What this is for, and what it is not

This is the premise sentence of the manuscript's
`\subsection{Undecidability of MF recognition}`:

> Lemma `lem:permanence`(1) and Theorem `thm:A` make MF a Markov property of
> finitely presented groups: the trivial group is MF, and by subgroup heredity
> the finitely presented group `E` embeds in no MF group.  The Adian--Rabin
> theorem therefore applies.

Everything up to "therefore" is asserted here and is machine-checked
unconditionally: `AdianRabinMarkovProperty.operatorMF_isMarkovProperty`, with
the heredity step isolated from MF as `forbidden_of_hereditary` and the
isomorphism-invariance clause — which the prose leaves implicit — proved
explicitly.  The coding half is `PresentationCodes.semantics` (interpretation,
`Primcodable`, finite presentation of every coded group) together with
`PresentationCodeCompleteness.exists_code_mulEquiv` (adequacy) and
`markovWitness`.

Nothing here asserts the Adian--Rabin theorem, the Novikov--Boone theorem, or
any reduction data standing in for them; that is
[[adian-rabin-transform-for-mf]], and the conclusion it buys is
[[mf-recognition-undecidable]].  Note also that "MF is a Markov property" is a
*premise*, not a consequence: it is exactly one of the four fields of
`MarkovMFConsequences.AdianRabinReduction`, and on its own it implies no
undecidability statement whatsoever.
