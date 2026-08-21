---
rg: 2
id: verifier-reflection-cancellation-proof
kind: route
title: Repeat one rejection projection twice
target: one-product-of-verifier-reflections-does-not-control-game-energy
requires: []
---

Take any nonzero projection `P` and set `L_1=L_2=P`.  The two verifier
reflections are both `R_i=I-2P`, so

```text
R_2R_1=(I-2P)^2=I.
```

Their product has zero fixed-vector defect on every vector.  But for every
nonzero Gram operator `G` with `PG=G`, the equally weighted positive game
Hamiltonian satisfies

```text
tr(G^*[(L_1+L_2)/2]G)/||G||_2^2=1.
```

This exact two-dimensional counterexample proves there can be no universal
implication from product fixedness to positive verifier energy.
