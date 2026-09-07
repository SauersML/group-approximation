# Non-MF manuscript repair status — 2026-09-07

These repairs were reconciled with main at `4b34d78a` (including the new
canonical K₁ material and Theorem F). This record is not a complete Lean
build attestation.

## Corrections

- **Lemma 2.1:** the C-star implication now requires an injective group
  homomorphism into the unitary group. Pairwise distinct indexed unitaries
  alone were insufficient. Its two exact Lean counterparts now prove the
  MF-target/corona kernel equivalence and the faithful representation
  implication, including a possibly nonunital corona embedding.
- **Theorem B:** the printed universal-group endpoint now uses an involution.
  `ElementaryDoubleSwap.lean` proves that `w₀₁ w₂₃ w₀₂²` has order two and
  normally generates the rank-four elementary group over every nontrivial
  unital ring. It also verifies both printed commutators. The independent
  order-four Weyl result remains available under its existing names.
- **Exposition:** the coefficient sum is bounded in absolute value; the
  universal ring is explicitly unital and associative; the purely infinite
  ring convention is explicit; and the finite-certificate discussion states
  that it does not supply concrete relators or numerical thresholds.
- **Coverage metadata:** stale sentence keys and obsolete/redundant badges
  were removed, current manifests regenerated, and two K₁ assignments moved
  to the new canonical endpoints. Torsion-free results requiring literature
  inputs are recorded as partial, rather than completely formalized.
- **Checking:** declaration existence and conditionality lookup now use
  qualified names, preventing an unrelated theorem with the same short name
  from satisfying a reference. Regression tests cover namespace collisions
  and `noncomputable section`. Both active manuscript contracts now require
  the current unit-group headline and universal-group endpoint.

## Completed local validation

Using Lean `v4.32.0` and the repository's `-DwarningAsError=true` option:

```sh
lake build GroupApproximation.Leavitt.ElementaryDoubleSwap
lake build GroupApproximation.Analysis.MFAlgebra \
  GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefinitions
```

Both builds succeeded, including their import dependencies. The sentence
census and unconditional-checker regression tests pass. All 49 selected
manuscript references resolve, including the two current required endpoints,
and all 49 satisfy the source-header closure check. All 33 numbered claims
pass the manifest consistency check. Lean reports only `propext`,
`Classical.choice`, and `Quot.sound` for the four new principal lemmas;
no `sorryAx` or additional axiom appears.

## Remaining verification work

The regenerated census has **636 sentences: 192 unassigned and 30 partial**.
These are coverage classifications, not a count of false mathematical claims.
The strict completeness gate correctly fails. Much of the newly unassigned
material belongs to Theorem F and the finite-dimensional fixed-point and
perfect-block proofs added while these repairs were underway. The wordwise
linear-certificate argument also lacks a complete sentence assignment.

Several torsion-free and regular C-star results still depend on literature
input propositions or proof-debt carriers. Updating a reference or a census
status does not discharge those obligations. The conditionality check still reports five new
assignment findings involving `FournierFacioParagraph` or
`HullCommonQuotientPrinted`. Fifteen stale census exceptions were removed,
and no new exceptions were added. No exception baseline, axiom
policy, completeness gate, or protected verification ref was relaxed.

The complete consuming `UniversalGroupSigma` module and the full repository
still require completed validation. The completed local builds above do not
establish a successful full build at the repair commit. The distribution PDF
was not rebuilt locally; the existing draft-PDF workflow rebuilds it on a
TeX push, while the attested release continues to require its stricter gates.
