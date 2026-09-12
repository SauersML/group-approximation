---
rg: 2
id: standard-type-thin-common-reflection-sector
kind: claim
title: A symmetric-group standard type has an arbitrarily thin canonical reflection defect
distinct_from:
  common-higher-rank-context-projections-are-syndrome-cylinders: that classifies projections common to elementary-abelian context algebras; this uses one nonabelian outer type and does not require the private context groups to intersect.
  literal-common-ghost-atom-classicalizes-contexts: that identifies a rank-one Fourier atom inside both full context algebras; here the defect lies in a separate common matrix-type packet, leaving the private context algebras unspecified.
  canonical-high-density-local-sector-groupifier: that still has to put the BCS relations on the common accepting carrier; this supplies the carrier and its exact density only.
---

**ESTABLISHED.**  For every `n>=3`, put `K=S_n` and let `rho` be its
standard irreducible representation on

```text
V={(z_1,...,z_n) in C^n:sum_i z_i=0},       dim(V)=n-1.       (STR1)
```

Let `p=z_rho in C[K]` be the primitive central type projection and let
`s=(1 2)`.  Inside the simple block `pC[K]p isomorphic to End(V)`, set

```text
e=p(1-s)/2,             q=p-e=p(1+s)/2.                       (STR2)
```

Then `e,q` are orthogonal algebraic projections summing to `p`, and for the
canonical trace normalized on the `p` corner,

```text
tau_p(e)=1/(n-1),       tau_p(q)=(n-2)/(n-1).                 (STR3)
```

Indeed `s` negates the line `C(e_1-e_2)` and fixes its codimension-one
complement in `V`.  Hence `(1-rho(s))/2` has rank one and
`(1+rho(s))/2` has rank `n-2`.  The normalized trace on a primitive
`M_(n-1)` Fourier block is normalized matrix trace, proving `(STR3)`.

Thus a single shared finite subgroup and literal reflection provide an
accepting carrier whose relative canonical deficit is arbitrarily small.
Unlike a shared one-ghost atom inside every elementary-abelian context, this
does not identify any private context group: only the outer packet `K`, its
type `p`, and the reflection `s` are common.

This is a density lemma, not a predicate compiler.  Ordinary group relations
still do not automatically enforce a nonlinear BCS only on `q`, and a
construction placing all context algebras back in `pC[K]p` would be finite
dimensional.  The required block-escaping payload is isolated in
`standard-reflection-sector-bcs-groupifier`.

