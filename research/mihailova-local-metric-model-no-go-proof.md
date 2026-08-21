---
rg: 2
id: mihailova-local-metric-model-no-go-proof
kind: route
title: Apply Alekseev-Thom to the residually finite direct-product actor
target: mihailova-left-right-local-models-do-not-see-q
requires: []
---

The actor `F_m x F_m` is residually finite.  Alekseev--Thom,
[*On finite local approximations of isometric actions of residually finite
groups*](https://arxiv.org/abs/2512.14147), Theorem 1.1, prove that every
isometric action of a residually finite group has finite local isometric
models.  Applied to the discrete metric left-right action `(MLM1)`, their
theorem gives, for finite `X_0 subset Q`, finite `A subset F_m x F_m`, and
`epsilon>0`, a finite metric space `(Y,eta)`, an exact isometric action of
`F_m x F_m` on `Y` (factoring through a finite quotient in their
construction), and `f:X_0->Y` such that

```text
| eta(g.f(x),h.f(y))
    - delta(g.x,h.y) | <= epsilon
```

for `g,h in A` and `x,y in X_0`.  The proof uses residual finiteness only of
the actor, never an approximation property of `Q`.  Taking `Q` to be the
established finitely presented nonsofic group proves that these local models
cannot imply soficity of `Q`.

Why this does not contradict the Mihailova nonseparability calculation is
visible in the definitions.  A residually finite transitive set action needs
one exact finite Schreier model preserving a prescribed finite equality and
inequality pattern.  A sofic set action needs approximate permutation laws
together with injective orbit charts at a `1-o(1)` proportion of model
points.  Alekseev--Thom instead permit an arbitrary finite invariant metric
and produce one local almost-isometric placement.  There is no common
Hamming population on which charts are replicated, so neither stronger
notion follows.

The same paper's introduction records the classical operator-algebraic
boundary (citing Brown--Ozawa, Theorem 6.2.7 and Exercise 6.2.4): the
permutation representation of the left-right action on `ell^2(Q)` is weakly
contained in finite-dimensional unitary representations of `F_m x F_m`
exactly when `Q` is hyperlinear.  This identifies the missing promotion
precisely.  Local finite metric actions are universal; finite-dimensional
approximation of the left-right **unitary coefficients** is equivalent to a
real approximation property of `Q`.
