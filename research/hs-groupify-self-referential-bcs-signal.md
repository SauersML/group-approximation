---
rg: 2
id: hs-groupify-self-referential-bcs-signal
kind: claim
title: Preserve the self-referential BCS signal while compiling its nonlinear predicates to group words
distinct_from:
  uniform-halting-pauli-word-oracle: that activates a growing Pauli test after a dimension-reporting halt; this groupifies one fixed finite self-referential BCS and needs no post-halting activation.
  multiplicity-return-transducer: that starts with an unmarked total forbidden-mass gap from a non-CE BCS; this must preserve one distinguished projection and return its signal through the predicate packets.
---

For the fixed BCS `(B_*,D)` of
`self-referential-bcs-nonzero-signal-collapse`, construct a finite
presentation `Gamma=<S|R>`, a marked word `w`, and constants `K,c>0` such
that:

```text
D!=0 in A(B_*)  =>  w!=1 in Gamma,                               (SGB1)
```

and every finite-dimensional unitary tuple `U` for `S` canonically yields a
strategy `S_U` for the BCS game with

```text
epsilon(S_U) <= K Def_R(U)^2,

phi_(S_U)(D) >= c ||w(U)-I||_2^2-K Def_R(U)^2.                   (SGB2)
```

The constants need only be effective for this one fixed BCS. Clause `(SGB1)`
is algebraic signal preservation; `(SGB2)` is normalized-HS payment. Together
they convert the self-referential BCS collapse into a nonhyperlinear group.

## Attempts

- Scalar selector relations cannot implement the arbitrary nonlinear BCS
  predicates, by `finite-selector-gadget-induction-barrier`.
- `boolean-predicate-is-one-rank-jump` and
  `predicate-rank-gate-doubles-restriction-multiplicity` compile every local
  predicate into a finite Schur--Clifford packet without deleting selector
  sectors. The remaining issue is to return the distinguished `D` carrier at
  fixed packet scale so that forbidden multiplicity pays `(SGB2)`.
- Unlike the dimension-reported Pauli route, no uniform growing query oracle
  is required. Unlike the generic non-CE multiplicity route, the marked
  signal itself prevents the construction from firing merely on a
  classically unsatisfiable CSP. This makes a marked version of
  `fixed-scale-contextual-multiplicity-holonomy` the narrowest current attack.
