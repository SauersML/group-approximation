---
rg: 2
id: branch-controlled-pauli-selector-reset-proof
kind: route
title: Evaluate the two central commutator controls on the q branches
target: branch-controlled-pauli-selector-reset
requires: []
---

Use the normal form in which all `z_i,J,q` are central and all reset
generators commute except for `(BPR1)`. The commutators lie in the elementary
abelian center, so collection terminates and gives a finite class-two group.

On `J=-1,q=-1`, relation `(BPR1)` reads

```text
s_i^- z_i=-z_i s_i^-,       s_i^+ z_i=z_i s_i^+.
```

On `J=-1,q=+1`, the two equations are reversed. Across distinct indices all
pairs commute. Hence the active family on either branch is the tensor product
of `k` Pauli pairs, generating `M_(2^k)`. Its commutant is scalar on that
selector/reset factor, so no old selector character remains as a central
label. Only the literal central bits `q` and `Jq` were used; no evaluation of
the original nonlinear predicate occurs in the reset relations.

