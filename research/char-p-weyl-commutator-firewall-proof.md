---
rg: 2
id: char-p-weyl-commutator-firewall-proof
kind: route
title: Differentiate the truncated polynomial module and apply complex trace cyclicity
target: char-p-weyl-blocks-local-commutator-decoder
requires: []
---

On the basis `1,t,...,t^(p-1)` of `F_p[t]/(t^p)`, multiplication `M` and
formal differentiation `D` obey

```text
(DM-MD)t^j=t^j
```

for every basis vector.  At the final vector the missing `t^p` term is
exactly repaired by `p=0`, so `DM-MD=1` without a boundary remainder.

The two standard Steinberg commutator formulas give `e_13(DM)` and
`e_13(MD)`.  Root additivity turns their quotient into `e_13(1)`.  Since
`R` is finite, `E_3(R)` is finite; its left regular representation is an
exact unitary realization and has the canonical delta trace.

For complex matrices, normalized trace annihilates every additive
commutator.  Cauchy--Schwarz against the identity therefore gives

```text
||[Y,X]-I||_2 >= |tr([Y,X]-I)|=1.
```

Hence the exact finite root packet cannot entail a unital complex additive
coefficient decoding.  Any successful use of the paired root word must add
a global relation or a genuinely finite-coordinate chart which rules out
this characteristic-`p` model.
