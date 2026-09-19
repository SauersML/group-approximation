---
rg: 2
id: psl2-bruhat-tits-action-soficity-forces-p-instability
kind: claim
title: Soficity of the PSL2 dyadic Bruhat--Tits vertex action forces flexible permutation instability
distinct_from:
  iwahori-local-global-defect-question: that is the open flexible Hilbert--Schmidt repair problem for unitary representations of the Iwahori amalgam; this is an unconditional implication from soficity of the vertex action to failure of permutation repair
  monomial-ascending-hnn-coset-action-sofic: that proves soficity for a nested finite-index ascending-HNN telescope; the dyadic PSL2 vertex stabilizer is co-dense and the Bass--Serre splitting has two vertices, so that theorem does not apply
  coordinate-action-not-sofic: that is Kun--Thom's proved nonsofic action; the status of this arithmetic vertex action remains open, and this claim identifies the exact permutation-stability consequence of a positive answer
artifacts:
  - research/artifacts/psl2-bruhat-tits-soficity-fork-2026-08-21.md
---

Put

```text
A=PSL_2(Z[1/2]),   C=PSL_2(Z),   X=A/C.
```

Then `X` is one color class in the vertex set of the 3-regular
Bruhat--Tits tree of `PGL_2(Q_2)`.  If `A action X` is a sofic action in the
Gao--Kunnawalkam Elayavalli--Patchell sense, then `A` is not flexibly
permutation-stable.

Indeed, finite actions of `A` factor through odd congruence quotients and
`C` surjects onto each quotient.  Selberg's congruence property `(tau)` gives
the uniform spectral gap on all of those finite actions.  Hence the pair
satisfies `codense-tau-coset-soficity-forces-permutation-instability`.

This settles neither side of the action question.  It gives a rigorous
falsification fork:

```text
prove flexible P-stability of A  =>  the tree action is nonsofic;
prove the tree action sofic      =>  an explicit noncorrectable sequence
                                     of permutation approximations of A.
```

