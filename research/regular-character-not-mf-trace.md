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

Two gaps separated this claim from that one.  **One of them is now closed.**

- **The definitional comparison — CLOSED 2026-08-17.**  It used to be true that
  nothing in the tree related the finite-test-set predicate above to Shulman's
  asymptotic condition on all of `C^*(E)`.  It no longer is.
  `Analysis/ShulmanTraceClasses.lean` transcribes her `IsMFTrace` verbatim —
  operator-norm asymptotic multiplicativity, linearity and `*`-preservation, a
  uniform bound, trace-correctness, and no positivity or unitality — and
  `Sofic/ShulmanMFTraceBridge.isOperatorMF_of_isMFTrace_canonicalMaximal`
  carries it to operator MF for the group, through the canonical trace of the
  *full* group C-star algebra built in
  `Analysis/MaximalGroupCStarTrace.lean`.  Composed at the literal group in
  `LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace`,
  the conclusion is now stated where the literature states it: about `tau_E`
  on `C^*(E)`, quantified over every element of the algebra.
- **The hyperlinear half** — still unformalized, and now the only thing between
  this development and [[hyperlinear-trace-not-mf-trace]].  It needs the
  tracial matrix ultraproduct of Shulman's reformulation remark.

The finite-test-set statement is kept as the primitive because it is what the
1298-line recognition theorem actually concludes; the trace-level statement is
its corollary, not a restatement of it.

Recorded because the repository was carrying the trace consequence entirely
outside Lean, and the half of it that is cheap to formalize was never
composed.

## The one blocker, and why the tempting shortcut does not take

The hyperlinear half needs `π : C^*(E) -> Q`, which needs
`maximalGroupCStar_existsUnique_lift`, which needs `[CStarAlgebra Q]` on the
tracial matrix quotient.  **That instance does not exist, and the pinned
Mathlib has no C-star-quotient instance at all** — nothing for
`Ideal.Quotient`, nothing under `Analysis/CStarAlgebra`.  So
`||x + J|| ^ 2 = ||x^* x + J||` has to be proved here.

**The shortcut that looks available, and why it fails.**
`Analysis/CStarSeminormQuotient.exists_isCStarNorm_on_quotient` produces a
C-star *norm* on `A / nullIdeal p` for a C-star seminorm `p`, without any
approximate unit.  One can even produce the right seminorm for the `omega`
version: let `tau_omega(x) = lim_omega tr(x_n)`, take its GNS representation,
and set `p(x) = ||pi_GNS(x)||`.  For a *tracial* state the kernel is exactly
`{x : tau(x^* x) = 0}` — because `tau(a^* x^* x a) = tau(x^* x a a^*) <=
||a a^*|| tau(x^* x)` — which is precisely the Hilbert--Schmidt-null ideal.  So
`isCStarSeminorm_iSup_starRep` applies and a C-star norm on the quotient
follows.

**But it is the wrong norm.**  What comes out is the GNS operator norm
`q(x) = p(g x)` on a chosen representative, not the hand-built quotient norm
already installed as `tracialMatrixQuotientNormedRing`
(`TracialMatrixUltraproduct.lean:472`, a `Submodule.Quotient` infimum).  The two
do agree — the C-star norm on a quotient is unique — but *proving* they agree is
the same theorem we were trying to avoid.  And adopting the GNS norm instead
would fork the normed structure: every quotient-representative lemma, the
`ultratraceCLM` bound and the completeness instance are all stated against the
existing norm, so a second norm bundle is a diamond that fails far from its
cause or, worse, typechecks and means something else.

**Consequence.**  The instance must be a `CStarRing` **mixin over the existing
normed structure**, proved by the approximate-unit route:
`||a + J|| = inf { ||a - a e|| : e in J, 0 <= e <= 1 }`, then the C-star
identity via `||(1-e) a^* a (1-e)|| <= ||a^* a (1-e)||`.  Only a per-`j`,
per-`epsilon` witness is needed rather than an approximate-unit net, which is
exactly the shape of
`HilbertSchmidtApproximateUnit.exists_projection_approximate_unit` (landed,
`c8f8768b`): `||j - j e||^2 <= t` together with `t * ||e||_2^2 <= ||j||_2^2`,
the second clause being what keeps the witness inside the ideal.
