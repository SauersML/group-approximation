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

Within an exact `R`-module, `q` is central. On `J=-1,q=-1`, `(BPR1)` reads

```text
s_i^- z_i=-z_i s_i^-,       s_i^+ z_i=z_i s_i^+.
```

On `J=-1,q=+1`, the two equations are reversed. Across distinct indices all
pairs commute. Hence the active family on either raw `q` branch is the tensor
product of `k` Pauli pairs, generating `M_(2^k)`, and all `z`-characters occur
equally there. This proof concerns the restriction to the finite reset group;
it makes no assertion that a raw `q` eigenspace is invariant under an
amalgamated packet factor.
