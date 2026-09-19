---
rg: 2
id: finite-group-opnorm-support-profile
kind: claim
title: A fixed finite-group operator-norm model has a stable finite support profile
distinct_from:
  gowers-hatami-finite-group-hs-stability: that gives flexible normalized-HS exactification for arbitrary finite groups and may change dimension; this is fixed-group same-dimension operator-norm correction and records zero-versus-positive irreducible support.
  near-regular-finite-character-fixes-plancherel-types: that uses canonical trace to force quantitative Plancherel multiplicities; this uses no trace and records only the discrete support subset.
  pure-finite-group-operator-scaling-collapses-to-multiplicity: that classifies a spectral intertwiner test between two already exact representations; this first corrects an approximate representation and proves its support type is well-defined.
---

Fix a finite group `H` and a finite presentation of it.  There are constants,
depending only on that presentation, such that every sufficiently accurate
operator-norm unitary model in `M_d(C)` is close, in the same dimension, to an
exact representation

```text
rho:H -> U(d).
```

Moreover, once the defect and correction radius are small enough, the subset

```text
Sigma(rho)={lambda in Irr(H): multiplicity of lambda in rho is positive}
```

is independent of the chosen correction.  Thus the exactified irreducible
support is a stable invariant taking values in the finite set
`P(Irr(H))`.  Operator norm detects the presence of even a rank-one sector;
no positive normalized-trace density is required.

This does not authenticate a sector by a group word.  Turning a central
group-algebra idempotent or a support predicate into word-level group syntax
is a separate compiler problem.
