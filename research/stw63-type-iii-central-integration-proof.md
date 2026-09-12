---
rg: 2
id: stw63-type-iii-central-integration-proof
kind: route
title: Disintegrate over the center and measurably select the factorwise unitaries
target: stw63-type3-separable-predual-vn-uniqueness
requires: []
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

The precise imported uniqueness theorem is Hua--White, Theorem A.1: if `A`
is separable, unital, and exact, `N` is a type-III factor with separable
predual, and two unital nuclear star homomorphisms `A->N` have the same
kernel, then they are norm approximately unitarily equivalent.  No UCT
hypothesis is present.

Write the standard central decomposition

```text
M = integral_X M_x dmu(x),
```

where `X` is a standard measure space and `M_x` is a type-III factor with
separable predual for almost every `x`.  Choose a countable dense star
subalgebra of `Z`.  Disintegrating the countably many algebraic identities
shows, after discarding one null set, that `phi` and `psi` give unital star
homomorphisms

```text
phi_x,psi_x:Z->M_x
```

for every remaining `x`.  Each map is injective because `Z` is simple.  It is
nuclear because `Z` is nuclear.  Thus the two maps have the same kernel and
Hua--White Theorem A.1 applies in every fiber.

Fix a finite set `F={a_1,...,a_k}` in `Z` and `epsilon>0`.  In each fiber the
set

```text
U_x={u in U(M_x):
     max_i ||u phi_x(a_i)u* - psi_x(a_i)|| < epsilon/2}
```

is nonempty.  In the standard Borel field of unit balls, the graph of this
multifunction is measurable: multiplication, adjoint, the given decomposable
sections, and the fiber norm are Borel.  The measurable-selection theorem for
standard Borel fields therefore supplies a measurable unitary section
`x->u_x` with `u_x in U_x` almost everywhere.  Its direct integral `u` is a
unitary in `M`, and the norm formula for decomposable operators gives

```text
max_i ||u phi(a_i)u* - psi(a_i)||
  = essSup_x max_i ||u_x phi_x(a_i)u_x* - psi_x(a_i)||
  <= epsilon/2 < epsilon.
```

Applying this to an increasing sequence of finite sets dense in the unit ball
of `Z` and tolerances tending to zero gives a sequence of implementing
unitaries.  The only inputs beyond Hua--White Theorem A.1 are standard central
disintegration and measurable selection for separable-predual von Neumann
algebras.
