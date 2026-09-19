---
rg: 2
id: sl3-building-deck-cocycles-round-coherently
kind: claim
title: Finite SL3 building quotients admit coherent permutation rounding of the dense arithmetic deck cocycles
artifacts:
  - research/artifacts/sl3-building-quotient-label-audit-2026-08-21.md
distinct_from:
  sl3-finite-building-quotients-forget-arithmetic-labels: that is the proved descent fence showing what unlabelled quotients omit; this asks for the extra simultaneous labelled rounding.
  sl3-canonical-double-has-a-correctable-vertex: that is a normalized-HS correction theorem for canonical double microstates; this is a finite permutation construction for the underlying coset action.
---

For every finite word window `W subset A=SL_3(Z[1/2])`, finite vertex
window `E subset A/C`, and `epsilon>0`, there is a finite quotient or finite
lift of the type-zero `SL_3(Q_2)` building with permutations `sigma_a` for
`a in W` and framed copies of `E` at at least a `(1-epsilon)` fraction of
its vertices such that:

```text
sigma_a sigma_b = sigma_(ab)
```

outside an `epsilon` fraction for every tested product, and the framed
copies are covariant under `sigma_a` whenever `x,ax in E`.

This is the simultaneous deck-gauge condition absent from unlabelled local
convergence.  It is stronger than independently choosing a representative
or matching for each Hecke correspondence.

## Attempts

Large-injectivity-radius quotients and random lifts reproduce the local
unlabelled affine building, but the descent lemma
`sl3-finite-building-quotients-forget-arithmetic-labels` shows that a fixed
arithmetic generator does not descend unless it normalizes the deck group.
Fixed Hecke adjacency also loses the label because left displacement is
conjugated by the moving frame.  The remaining attack is therefore a
simultaneous approximate gauge choice with vanishing holonomy on each
finite word window; no construction or amplification-stable obstruction is
currently known.
