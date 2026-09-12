---
rg: 2
id: clifford-radical-antiphase-capacity-proof
kind: route
title: Push each failure character through its local Clifford frame and count the target dual
target: clifford-radical-antiphase-routing-has-character-capacity
requires:
  - full-v4-latent-coordinate-has-an-operator-five-fourths-floor
---

Write the branch transport on Weyl labels as an invertible linear map
`S_i:D->D`.  Conjugation by its Pauli gauge contributes a linear sign
functional `t_i in D^*`.  If local axis `v` is sent to target axis
`w=S_i v`, then the local failure character contributes `chi_i(v)` and the
gauge contributes `t_i(v)`.  Consequently

```text
a_i(w)=(chi_i+t_i)(S_i^(-1)w)
```

is one well-defined element of the common target dual.  Multiplying a local
word by the marked sign only changes the common scalar phase on that edge and
cancels when the two source phases are compared.  Thus opposite phases on
edge `ij` are precisely `(CRAC2)`.

A nonzero linear functional on `D` takes the value one somewhere, whereas the
zero functional never does.  Hence an edge axis exists if and only if
`a_i+a_j` is nonzero.  Completeness of the comparison graph forces the `a_i`
to be pairwise distinct, proving `(CRAC3)`.

The exact V4 failure triples `(VOF2)` contain five ones over four atoms, so
the branch-occurrence multiset has size five.  Apply `(CRAC3)` with `r=2`.
For a dummy extension by `F_2^t`, every old atom has `2^t` refinements and
every occurrence is refined the same way, giving `(CRAC5)`.  The accompanying
script exhausts all `4^5=1024` effective-character assignments at `r=2`,
finds the sharp four-branch witness, finds no five-branch witness, and checks
the dummy-extension count through rank six.
