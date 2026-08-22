---
rg: 2
id: two-holonomy-weyl-controller-has-vanishing-boundary-defect
kind: claim
title: A fixed Weyl commutator hides its entire defect in one cyclic boundary
distinct_from:
  tensor-separated-holonomy-controller-is-circular: that treats an arbitrary independent hyperlinear holonomy group abstractly; this gives the sharp explicit clock-shift countermodel for the strongest scalar two-holonomy relation.
  commuting-automorphism-cocycle-forces-multiplicity: that derives a fixed divisibility condition from finite projective holonomy; this shows directly that even a phase with no exact finite model has vanishing normalized-HS defect.
  sl3-hnn-fold-determinant-and-index-are-trace-blind: that realizes arbitrary trace-zero determinant-one commutators; this estimates approximation of a prescribed scalar commutator phase on a positive losing carrier.
---

**ESTABLISHED NO-GO.**  Fix any phase `zeta in T`.  For every `d>=1` there
are clock-shift unitaries `S_d,D_d in U(d)` satisfying

```text
||S_d D_d S_d^-1-zeta^-1 D_d||_2
   =|zeta^d-1|/sqrt(d) <=2/sqrt(d).                     (TWC1)
```

If `zeta` has finite order `m`, the defect is exactly zero whenever `m|d`.
Thus a two-holonomy controller which tries to charge a losing carrier `E` by
the fixed Weyl relation

```text
A B A^-1=zeta^-1 B                                     (TWC2)
```

has amplified squared defect at most

```text
4 tau(E)/d.                                            (TWC3)
```

It cannot imply a dimension-independent lower bound `c tau(E)`.

The only visibly `A,B`-dependent carrier in this construction is the cyclic
wrap boundary, and it has relative rank `1/d`.  Spectrally selecting that
boundary therefore loses exactly the positive density needed by the Fanizza
terminal criterion.  Repeating fixed-size blocks does not help: finite-order
phases have exact blocks, while for an arbitrary phase the block size may tend
to infinity with the matrix dimension.

Adding a property-(T), expander, or finite-presentation wrapper around the two
holonomies does not change this conclusion if the resulting holonomy group is
hyperlinear: `tensor-separated-holonomy-controller-is-circular` tensors its
canonical microstates onto the losing carrier.  If the wrapper is
nonhyperlinear, it has imported the desired obstruction.  Hence neither a
fixed scalar commutator nor expansion of an independent two-holonomy factor
is the missing payload coupling.

