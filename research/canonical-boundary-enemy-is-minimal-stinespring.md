---
rg: 2
id: canonical-boundary-enemy-is-minimal-stinespring
kind: claim
title: The exact canonical HNN boundary enemy is already a minimal Stinespring dilation
distinct_from:
  canonical-hnn-flat-boundary-enemy: that constructs the exact flat boundary enemy; this proves its ambient dilation has no redundant summand and is canonical up to Stinespring unitary equivalence.
  canonical-exact-polar-models-have-flat-singular-loss: that records flat finite-dimensional polar calibrations without addressing minimality of their simultaneous multiplicative dilation.
  determinant-index-cannot-authenticate-julia-heat-overlap: that rules out bounded index authentication for a different Julia heat cell; this is an exact minimal-dilation obstruction at the arithmetic fold interface.
---

**ESTABLISHED.**  In `canonical-hnn-flat-boundary-enemy`, define the ucp map

```text
Phi:C*(A)->B(L2(G)),
Phi(u_a)=f(a) lambda_G(a),
f(a)=<lambda_Q(q(a))xi,xi>.                              (CMS1)
```

The displayed dilation

```text
K=L2(G) tensor ell2(Q),
pi(a)=lambda_G(a) tensor lambda_Q(q(a)),
V eta=eta tensor xi                                      (CMS2)
```

is the minimal Stinespring dilation of `Phi`.  Hence the fixed boundary
leakage

```text
tau(P)^(-1)tau(P pi(s)^*(1-P)pi(s)P)=1-|f(s)|^2          (CMS3)
```

does not live in a removable redundant summand.  Minimal Stinespring
uniqueness carries it to every other minimal dilation.

In particular, requiring the exact ambient dilation in the arithmetic fold
argument to be minimal, canonical up to unitary equivalence, or the minimal
Naimark dilation of the coefficient kernel does **not** turn boundary
leakage into presentation defect.  The enemy still has the exact canonical
regular retained HNN tuple, zero relator defect, and boundary
`1-alpha^2` on every named generator.

This leaves a narrower possible positive theorem: a matrix microstate may
admit some other dilation selected using finite-dimensional/CE structure
and the two vertex tuples jointly.  Minimality of the ucp compression alone
provides no such selection.  Separate generatorwise Julia dilations do not
improve this conclusion: they are not a simultaneous multiplicative
dilation of `C*(A)`, whereas `(CMS2)` already is one and is minimal.

