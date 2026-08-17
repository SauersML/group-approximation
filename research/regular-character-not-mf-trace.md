---
rg: 2
id: regular-character-not-mf-trace
kind: claim
title: The regular character of the literal group is not an MF trace
distinct_from:
  hyperlinear-trace-not-mf-trace: That is the statement in Shulman's vocabulary — an asymptotic condition on every element of a C-star algebra, together with the hyperlinear half — and answering his question needs both halves plus a definitional comparison. This is only the negative half, in the finite-test-set form on the group unitaries that the Lean actually proves.
  regular-character-mf-trace-implies-group-mf: That is the general recognition theorem, an implication with the group quantified. This is its instantiation at one explicit group, where the conclusion is refuted and so the hypothesis is too.
  literal-group-fails-mf-conventions: That records failure of the operator-norm MF conventions for the group. This records failure of a trace-level condition, which is a statement about matrix models of the canonical trace of the group C-star algebra rather than about embeddings of the group.
artifacts:
  - GroupApproximation/Sofic/LiteralTraceConsequence.lean
  - GroupApproximation/Sofic/MFTraceRecognition.lean
---

ESTABLISHED, unconditionally.
`LiteralTraceConsequence.markedGroup_not_isMFRegularCharacter`:

    ¬ MFTraceRecognition.IsMFRegularCharacter MarkedGroup

for `MarkedGroup` the literal finitely presented group `E`.  The packaged form
`markedGroup_sofic_hyperlinear_not_isMFRegularCharacter` adds the three group
facts the manuscript prints beside it: `E` is finitely presented, sofic, and
hyperlinear.

## What the predicate says

`IsMFRegularCharacter G` unfolds to: there is a bound `B : G -> R` such that
every finite test set `F` and every `eps > 0` admit a matrix model of the
regular character on `F` — a norm bound by `B`, operator-norm multiplicativity
and star-compatibility to within `eps`, normalized trace within `eps` of `1` at
the identity and within `eps` of `0` away from it.

It is the **local, group-unitary** form of the MF-trace condition for the
canonical trace of the full group C-star algebra.  It is deliberately not
Shulman's condition, which is asymptotic and quantifies over every element of
the algebra rather than over the group elements.

## The proof is one composition

Three theorems already in the tree, no new analysis:

1. `MFTraceRecognition.isNormApproximable_of_isMFRegularCharacter` — the
   recognition theorem.  The trace clause at `1` pins a macroscopic unit corner
   by spectral rounding of the hermitian part of the model unit; inflation by
   the corner complement and polar correction produce exact unitaries; the
   trace clause away from `1` gives separation `sqrt 2`, which the operator
   norm dominates.  This is the substantive input, 1298 lines.
2. `OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one` and
   `isCDEOperatorMF_iff_isOperatorMF` — the two convention bridges.
3. `LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF` — Theorem A
   for the literal group.

## What is NOT established here

The hyperlinear half.  There is no `HyperlinearTrace` predicate anywhere in the
tree, no tracial ultraproduct object, and no Bartle--Graves.  "There exists a
hyperlinear trace which is not MF" is therefore **not** a Lean theorem; it is
[[hyperlinear-trace-not-mf-trace]], carried by a written proof route.

Two gaps separate this claim from that one, and they should be named
separately:

- **the hyperlinear half**, unformalized;
- **the definitional comparison**, between the finite-test-set predicate above
  and Shulman's asymptotic condition on `C^*(E)`.  Nothing in the tree relates
  them, and the same comparison is what stands between us and the shorter
  Schafhauser Proposition 2.2 route recorded in
  [[hyperlinear-trace-not-mf-trace]].

Recorded because the repository was carrying the trace consequence entirely
outside Lean, and the half of it that is cheap to formalize was never
composed.
