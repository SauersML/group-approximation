---
rg: 2
id: lef-implies-operator-mf
kind: claim
title: Local embeddability into finite groups implies operator MF
distinct_from:
  mf-positive-controls: That records subgroups, residually finite groups and locally finite groups as MF; this is the common generalization of the last two, and it is the form the telescope-core arguments actually need.
  countable-group-mf-conventions: That establishes the equivalence of the MF formulations; this supplies a new sufficient condition for the property they all share.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LocallyFiniteMF.lean
  - GroupApproximation/Sofic/OperatorMFPositiveControls.lean
---

Every countable LEF group is operator MF, in the norm-matrix-corona sense of
`countable-group-mf-conventions` — hence in every formulation equivalent to it
there (weak, actual-corona, unitary-sequence, local, increasing-dimension,
ultraproduct, finite-set, group-theoretic, ambient-unitary).

This is the manuscript's `lem:rfmf`/`lem:lfmf` argument with its hypothesis
weakened to exactly what that argument uses.  At coordinate `n`, take a local
embedding of the `n`-th window into a finite group `Q_n` and use the left
regular representation of `Q_n`.  Multiplicativity is exact for every pair in
the window, because the local embedding is a partial homomorphism there;
separation is the same `sqrt 3` bound, because left translation by a
nonidentity element of a finite group is a fixed-point-free permutation.  An
exhausting sequence of windows then makes the induced corona map injective.

Reusable corollary chain: *locally residually finite* implies LEF (each finite
window sits in a finitely generated subgroup, which is residually finite, so a
finite quotient of it embeds the window), hence sofic and MF.  That is the form
used by `literal-telescope-core-lef` and available to any other lamp-by-telescope
argument, including `lamp-telescope-base-is-lef`.
