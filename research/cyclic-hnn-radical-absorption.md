---
rg: 2
id: cyclic-hnn-radical-absorption
kind: claim
title: A cyclic HNN relation turns a normally generated relative MF radical into an intrinsic full radical
distinct_from:
  cyclic-mf-quotient-phase-transition: That is an existence result from a different seed; this gives a reusable HNN criterion and computes the intrinsic radical of its kernel.
artifacts:
  - research/artifacts/sofic-cyclic-mf-quotient.md
---

Let E be countable, B normal in E, and suppose every MF homomorphism out
of E kills B. Suppose r in E and d in B have infinite order, r normally
generates E/B, and normalClosure_E(d)=B. Put
P=<E,s | s r s^-1=d>, and let chi:P->Z kill E and send s to 1.
Then N=ker(chi)=normalClosure_P(d)=Rad_MF(P)=Res_fin(P), and
Rad_MF(N)=N. For every normal R in P, Rad_MF(P/R)=NR/R, and P/R
is MF if and only if d belongs to R, equivalently P/R is cyclic.

This is a written theorem, not a new Lean endpoint.
