---
rg: 2
id: finite-simple-rr0-algebras-have-stable-rank-one
kind: claim
title: Every finite simple unital C*-algebra of real rank zero has stable rank one
---

Let `C` be a unital simple C\*-algebra of real rank zero with finite unit.  Must
`tsr(C) = 1`?

Status: Rordam (*The real rank of certain simple C\*-algebras*, 2005, page 1):
"It is not known if there are finite simple C\*-algebras of real rank zero and
stable rank > 1."  A brief search on 2026-09-12 found no later resolution; the
search was not exhaustive.

A positive answer gives cancellation, hence weak cancellation
(`finite-simple-rr0-weak-cancellation-via-stable-rank-one`), hence Problem XXIX.

## Attempts

* Any counterexample to XXIX gives a counterexample here in the strongest
  form.  Its finite corners have infinite stable rank
  (`stw29-counterexample-level-two-fingerprint`(b)), since `M_2` of the corner is
  infinite and Rieffel's matrix formula transports `tsr = infinity` down.
* In the nuclear, separable, non-elementary case, a positive answer to STW XXX
  would give it: Rordam's theorem that simple unital `Z`-stable algebras have
  stable rank one or are purely infinite.  No route is recorded, because the
  present claim has no nuclearity hypothesis.
* Villadsen's second-type algebras have prescribed stable rank `> 1` but
  are not of real rank zero (Rordam 2005, page 1, citing Villadsen, JAMS 1999).
  As for XXIX, the obstruction to cutting projections is the same Euler-class
  survival on generic zero sets.
