---
rg: 2
id: fano-pruning-is-line-hitting-empty-link
kind: claim
title: Distance-two commutation yields Fano caps exactly after a line-hitting empty-link condition
distinct_from:
  commuting-neighborhood-pruning-pays-atom-mass: that gives the operator inequality once a commuting neighborhood has no joint extension; this identifies the finite incidence condition needed to hit every Fano line.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks whether the published halting strategy admits cap supports; this gives a sufficient finite test but does not prove it for those instances.
---

**ESTABLISHED FINITE SUFFICIENT CONDITION.**  Let a finite CSP have context
PVMs, exact overlap consistency, and the following distance-two
oracularity property: for each context `c`, the PVM algebras of all contexts
in its constraint-neighborhood `N(c)` commute mutually.

For `a in R_c`, define `Link(c,a)` to be the set of tuples
`(b_d)_(d in N(c))` such that every `b_d in R_d`, all assignments agree on
every common variable, and every `b_d` agrees with `a` on `c intersection d`.
Then

```text
Link(c,a)=empty  =>  P_(c,a)=0.                              (FEL1)
```

Consequently, for an `R_*` context, if

```text
for every translated Fano line L subseteq R_c
there exists a in L with Link(c,a)=empty,                     (FEL2)
```

then the positive spectral support in context `c` is a Fano cap.  If
`(FEL2)` holds at every context, the entire perfect strategy has a Fano-cap
support profile.

Condition `(FEL2)` is finite and purely combinatorial.  It is the precise
extra input missing from “2-oracularizable implies Fano-prunable.”
Distance-two commutation constructs the joint refinement; it does not make
any link empty.

