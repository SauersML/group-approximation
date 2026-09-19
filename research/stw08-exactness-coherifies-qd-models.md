---
rg: 2
id: stw08-exactness-coherifies-qd-models
kind: claim
title: Exactness coherifies quasidiagonal finite-dimensional models
distinct_from:
  stw08-af-embedding-iff-summably-coherent-fd-models: that established theorem identifies coherence with AF-embeddability; this is the still-open assertion that exactness supplies coherence for a quasidiagonal algebra.
  stw99-problem-viii-exact-quasidiagonal-af-embeddable: that is the AF-embedding formulation; this is its finite-model coherence formulation.
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

Every separable exact quasidiagonal C\*-algebra admits a finite-dimensional
model system satisfying the summable coherence criterion in
`stw08-af-embedding-iff-summably-coherent-fd-models`.

This is open and is exactly Problem VIII in finite-model form.

## Attempts

Quasidiagonality supplies the asymptotic multiplicativity and isometry lines
but no connecting homomorphisms.  Replacing the next model by a block sum with
the preceding model does not work: an injective connecting homomorphism
preserves the norm of every old multiplicative defect, so the old block can
never be retired.  Exactness supplies local liftability and nuclear embeddings
into suitable ambient algebras, but neither gives the required summable
point-norm conjugacy between consecutive finite-dimensional models.  Existing
UCT proofs provide precisely this sort of global compatibility through
classification/stable-uniqueness input; removing that input is the unresolved
step.
