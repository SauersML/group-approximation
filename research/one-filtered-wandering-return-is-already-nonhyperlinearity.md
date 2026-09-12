---
rg: 2
id: one-filtered-wandering-return-is-already-nonhyperlinearity
kind: claim
title: One positive type-filtered wandering return already proves nonhyperlinearity
distinct_from:
  type-filtered-wandering-moments-sum-rejection-mass: that sums all forbidden types and invokes the game gap; this observes that any one nonzero filtered return is already a terminal canonical-trace contradiction.
  finite-subgroup-type-exclusion-is-already-nonhyperlinearity: that kills the mass of one finite-subgroup type; this permits the type mass to remain positive but forces one wandering word to return on it.
  residually-finite-models-refute-filtered-wandering-return: that gives exact finite quotient countermodels; this is the more general hyperlinear obstruction.
---

Let `Gamma` contain a finite subgroup `H`, let `P in C[H]` be a nonzero
projection, and let `r in Gamma`.  Suppose

```text
tau_Gamma(P r)=0.                                      (OFW1)
```

If there are `c>0` and a modulus tending to zero such that every canonical-
trace matrix microstate satisfies

```text
Re tr(P(U) r(U)) >= c tr(P(U))-o(1),                  (OFW2)
```

then `Gamma` is nonhyperlinear.

Indeed, the canonical trace is faithful on the finite-dimensional algebra
`C[H]`, so

```text
tau_Gamma(P)=tau_H(P)>0.                              (OFW3)
```

If `Gamma` were hyperlinear, canonical microstates would converge on the
two fixed group-algebra elements `P` and `P r`.  Equations `(OFW1)--(OFW3)`
would make the left side of `(OFW2)` tend to zero and its main right-hand
term tend to `c tau_H(P)>0`, a contradiction.

The supportwise normal-form condition used in the type-filtered actuator is
more than enough for `(OFW1)`.  If

```text
P=sum_(g in H) a_g g
```

and every `g r` with `a_g!=0` is nonidentity, then every summand has zero
canonical trace and hence `tau_Gamma(P r)=0`.

In particular, for `P=q_lambda F` with `q_lambda` a primitive central
idempotent and `F` a commuting forbidden projection, **one** nonzero
filtered actuator is already terminal.  It is unnecessary to construct an
actuator for every marked type or to sum rejection mass before obtaining the
nonhyperlinearity contradiction.  Exhaustive type summation remains useful
only if the available inequalities are coupled so that no individual
positive filter has a standalone wandering return.

This is also a circularity firewall.  A construction satisfying `(OFW2)`
cannot be justified solely by a hyperlinearity-preserving attachment to a
hyperlinear packet base: proving the matrix-only return is itself a proof
that the resulting group is nonhyperlinear.
