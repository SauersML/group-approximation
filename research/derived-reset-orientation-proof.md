---
rg: 2
id: derived-reset-orientation-proof
kind: route
title: Compute the duplicated controller restriction rows
target: derived-reset-does-not-fix-controller-orientation
requires: []
---

Fix the `J=-1` Pauli spin `rho` and an `r`-character `epsilon`.  If
`epsilon=+1`, Schur's lemma gives `c=uI`; if `epsilon=-1`, `cZ` commutes with
the Pauli spin, so `c=uZ`, with `u=+-1`.  Thus the four controller simples
`sigma_(epsilon,u)` restrict to the two edge simples `tau_epsilon` with
matrix

```text
[1 0]
[1 0]
[0 1]
[0 1].
```

The intended and opposite orientations are the duplicated rows.  The
balanced derived reset has the same restriction multiplicity on its old and
fresh types, so tensoring or Morita matching multiplies every row by the same
factor and leaves the duplication unchanged.  Equivalently, the character
twist `c -> -c` is trivial on the edge.

A literal reset translation has normalized trace zero, whereas the intended
controller has trace `(1+tr(r))/2` and equals the identity when `r=I`; hence
identification would break the perfect model.  Finally, if
`H=H_0 tensor v` and `c=(P_0+P_1r) tensor u`, the balanced word `HcHc`
retains `vuvu`.  The reset table imposes no relation on that commutator.
Therefore neither derivedness nor equal-scale reset data selects the
orientation.
