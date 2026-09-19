---
rg: 2
id: operator-mf-is-a-markov-property-proof
kind: route
title: Assemble the three clauses, then push them along an adequate coding
target: operator-mf-is-a-markov-property
requires: []
artifacts:
  - GroupApproximation/Computability/AdianRabinMarkovProperty.lean
  - GroupApproximation/Computability/OperatorMFMarkovWitness.lean
  - GroupApproximation/Computability/PresentationCodes.lean
  - GroupApproximation/Computability/PresentationCodeCompleteness.lean
---

## Why sufficient

Machine-checked with no `sorry`, no axiom, and no tagged literature premise.
The declarations, in the order the claim states them:

- **isomorphism invariance** — `operatorMF_isoInvariant`, by pulling MF back
  along the inverse isomorphism (`IsOperatorMF.comap` on an injective map);
- **subgroup heredity** — `operatorMF_hereditary`, manuscript Lemma
  `lem:permanence`(1) in `GroupProperty` form: restrict an injective corona
  representation;
- **the abstract heredity-to-forbidden step** — `forbidden_of_hereditary`,
  stated for an arbitrary group property so that the MF-specific content is
  visibly only heredity: if `P` is hereditary and `E` fails `P`, then no
  injection `E -> H` exists for `H` satisfying `P`;
- **the positive witness** — `OperatorMFMarkovWitness.positive_punit`: the
  trivial group is finitely presented and MF (through the finite case);
- **the forbidden witness** — `chosen_forbidden_subgroup`, the specialization
  of the previous two to the repository's chosen finitely presented non-MF
  group, and `exists_finitelyPresented_forbidden_subgroup` in existence form;
- **assembly** — `operatorMF_isMarkovProperty : IsMarkovProperty
  operatorMFGroupProperty`, one field per clause.

The passage from groups to codes:

- `PresentationCodes.PresentationCode := N x List (List (N x Bool))` — a
  generator count and a list of relator words, each a list of signed generator
  indices.  Two totality choices keep interpretation a *total* function: the
  generator count is stored offset by one, so the alphabet is never empty, and
  a letter index is read modulo the alphabet size.  Neither costs anything,
  because the coding has to be onto finite presentations, not injective;
- the type is `Primcodable`, so "computable transformation of finite
  presentations" acquires a referent, and `semantics :
  FinitePresentationSemantics PresentationCode` proves every coded group is
  finitely presented;
- `PresentationCodeCompleteness.exists_code_mulEquiv` — adequacy, proved by
  reading the presentation off `IsFinitelyPresented` itself: it unfolds to a
  surjection from a free group on `Fin n` with kernel the normal closure of a
  finite set, so the finite set is encoded letter by letter and the quotient
  identified.  The degenerate `n = 0` case, which forces the group trivial, is
  handled by `trivialCode` separately because the coded alphabet is never
  empty;
- `markovWitness : MarkovWitness (operatorMFProperty semantics)` — the two
  group-level witnesses transported across adequacy.

## Where the boundary is drawn

Three of the four fields of `MarkovMFConsequences.AdianRabinReduction` are
inhabited by the above: the `Primcodable` code type, the semantics, and the
Markov witness.  The fourth — a computable `transform` together with its
correctness equivalence — is deliberately *not* claimed here and is not
smuggled in as data anywhere in this route's Lean chain.  That is the content
of [[adian-rabin-transform-for-mf]].
