---
rg: 2
id: deligne-maslov-sector-traces-are-central-regular
kind: claim
title: Every trace in a nontrivial Deligne Maslov sector is a mixture of the two central-regular traces
distinct_from:
  deligne-twisted-fibres-have-no-amenable-trace: that excludes amenable traces using C-star property T and finite-dimensional invisibility; this classifies all traces in the fibre using higher-rank character rigidity.
  maslov-sector-tracial-generator-ucp-liftability: that asks for coordinate ucp lifts of a matricial ultraproduct homomorphism; this fixes the trace profile of every such homomorphism but does not provide those lifts.
---

Let `E_3` be Deligne's triple cover of `Sp_4(Z)`, let `z` generate its
order-three covering kernel, and fix `omega != 1` with `omega^3=1`.  The
center of `E_3` is the six-element inverse image of `{+I,-I}`.  There are
exactly two central characters `eta_+`, `eta_-` extending
`z |-> omega`.

Every tracial state on the twisted fibre

```text
A_omega = C^*(E_3)/(z-omega)
```

is a convex combination of the two central-regular traces

```text
tau_eta(g) = eta(g)  if g in Z(E_3),
             0       otherwise.                         (CR1)
```

Equivalently, after cutting by the remaining central order-two direction,
each of the two full-central-character fibres has a unique tracial state.
In particular every homomorphism from a nontrivial Maslov fibre to a tracial
matrix ultraproduct is automatically trace-preserving on each such central
summand.

This does not prove that either trace is Connes embeddable or amenable.  It
removes arbitrary trace profiles from the analytic problem: a surviving
Maslov microstate is necessarily a matricial model of one of the canonical
central-regular traces.

The proof is `deligne-central-regular-trace-classification-proof`.
