---
rg: 2
id: qutrit-psync3-tensor-closure-proof
kind: route
title: Tensor four admissible scalar qutrit interfaces back into the omega sector
target: qutrit-psync3-tensor-closure-obstruction
requires: []
---

For a scalar third root `z`,

```text
Pi_0(z)=(1+z+z^2)/3
```

equals one for `z=1` and zero for `z=omega,omega^2`.  Consequently each of
the four scalar pairs displayed in the target satisfies the completeness
hypothesis.  Choose its promised exact extension `rho_i`; amplification does
not change the scalar interface values.

The tensor product representation

```text
rho=rho_1 tensor rho_2 tensor rho_3 tensor rho_4
```

evaluates every group word as the tensor product of its four evaluations.
It therefore has zero relator defect.  Its central character is
`omega^4=omega`, so `(PS3-1)` applies.  Direct multiplication of the scalar
interfaces gives `rho(u)=1` and `rho(v)=omega`.  Hence its projector distance
is `||I-0||_2^2=1`, contradicting the zero right-hand side of `(PS3-1)`.
