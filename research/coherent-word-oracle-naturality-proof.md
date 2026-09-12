---
rg: 2
id: coherent-word-oracle-naturality-proof
kind: route
title: Induct over the coherent query calculus and expose the missing trace primitive
target: coherent-word-oracles-cannot-branch-on-their-own-tracial-profile
requires:
  - amplification-natural-words-cannot-read-packet-multiplicity
  - post-candidate-nemesis-has-a-finality-dilemma
---

For a word `w`, both identities `(CWO1)` follow by induction on word length.
They are preserved by linear combinations, products and adjoints.  Continuous
functional calculus preserves reducing direct sums and identity
amplification; the same is true for a spectral projection or polar sign when
the fixed gap makes that operation defined.  Tensoring a fixed finite control
space distributes over the unknown representation direct sum, and every
controlled gate acts independently on those reducing summands.  Induction on
the finite circuit proves `(CWO1)`.

Normalized traces and measurement probabilities are obtained only after
applying the external tracial state.  There is no operation in the induction
which turns that scalar into a central matrix and then controls on it.
Measurement without postselection is just another block decomposition;
postselection is nonlinear and is not a group equation.  Finally expand

```text
(U direct-sum V) tensor (U direct-sum V)
```

to see the two cross tensor blocks, proving that a tensor-cloning oracle lies
outside the one-copy calculus.  A separately named commuting representation
may be chosen correlated or reducible and therefore supplies no universal
replacement.  These observations prove the stated boundary.
