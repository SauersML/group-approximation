---
rg: 2
id: full-reset-makes-q-masa-negative-regular
kind: claim
title: The full Schur reset makes the flip-free q-MASA character vector negative-regular
---

Let `Rhat_f` be the translation-symmetrized full Schur reset, assume `f` is
nonconstant, and use the reset-ray parameter `n` of `(TFS5)`. For the
flip-free endpoint

```text
K_f=<J,q_1,...,q_N,q_(N+1)>,       D=2^N,
```

write `lambda_(K_f)^-` for the sum of all one-dimensional characters of
`K_f` on which `J` acts by `-1`, each once. Every exact `J=-1`
representation `rho` of `Rhat_f` satisfies

```text
Res_(K_f) rho = 2^(k+1)n lambda_(K_f)^-.                 (FQR1)
```

In particular, every one of the `2D` negative `K_f` characters has the same
multiplicity. The complete flip-free endpoint character vector is therefore
independent of which selector assignments satisfy `f`.

This does not contradict the sectorwise branch-separation theorem
`full-q-masa-forgets-selectors-retains-branches`: the words `Q_x` still have
disjoint supports on the two child simples before selector sectors are
aggregated. Formula `(FQR1)` says that the full translation and branch reset
averages those disjoint supports to the negative regular character. Hence a
reset atlas cannot first impose the full reset and then expect the bare
`K_f` character vector to carry the predicate-oriented Schur surplus through
a proper corner. It must transport sector-labelled child data before this
averaging, or retain an additional predicate-density element outside
`C[K_f]` and couple the one-sided actuator to that element.

