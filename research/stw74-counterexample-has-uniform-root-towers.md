---
rg: 2
id: stw74-counterexample-has-uniform-root-towers
kind: claim
title: Every LXXIV counterexample contains projective-free unit-root towers with uniform multiplicity
distinct_from:
  stw74-counterexamples-are-unstably-projectionless: that produces the full projectionless hereditary corner; this shows finite-unit-root failure persists uniformly through compactly contained spectral cutdowns in that corner.
---

Suppose `A` is a counterexample to Problem LXXIV, and let `D` be the full
projectionless hereditary subalgebra supplied by
`stw74-counterexamples-are-unstably-projectionless`.  For every nonzero
`a in D_+`, there are a rapidly increasing sequence

```text
0!=x_1 << x_2 << ... ,       sup_k x_k=[a],
```

and one integer `n>=1` such that, for every `k`,

```text
n x_k=[1_A],
```

while `x_k` dominates no nonzero class represented by a projection.

Thus neither passing to a compactly contained submodule nor taking a spectral
cutdown removes the projective-root obstruction; it occurs with a uniform
finite multiplicity on an entire tail.
