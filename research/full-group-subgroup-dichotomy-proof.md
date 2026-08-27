---
rg: 2
id: full-group-subgroup-dichotomy-proof
kind: route
title: Compute the fixed-point character and the Cartan expectation
target: full-group-subgroup-trace-generation-dichotomy
requires: []
---

The Feldman--Moore kernel of `v_g` is the characteristic function of the graph
of `g`.  Its diagonal coefficient is therefore the characteristic function of
`Fix(g)`, giving

```text
tau_R(v_g)=mu(Fix(g)).
```

The canonical trace of `L(Lambda)` is zero on every nonidentity group element,
so the full-group representation is trace preserving exactly when every
nonidentity element acts with null fixed set, i.e. when the action is
essentially free.

In that case the family `{v_g}` is orthonormal in `L^2(L(R),tau_R)`, and the
group-algebra map extends to a trace-preserving normal embedding of
`L(Lambda)`.  The Cartan conditional expectation satisfies

```text
E_A(v_g)=1_Fix(g)=0              (g != e),
```

while `E_A(v_e)=1`.  Hence for every `x` in the generated group von Neumann
algebra, `E_A(x)=tau_R(x)1`.  If such an `x` also belongs to `A`, then
`x=E_A(x)` is scalar.  Since `A=L^infinity(X)` is diffuse and contained in
`L(R)`, the generated group algebra is a proper subalgebra of `L(R)`.  This is
the claimed dichotomy.

