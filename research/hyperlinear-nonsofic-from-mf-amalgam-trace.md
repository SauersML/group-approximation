---
rg: 2
id: hyperlinear-nonsofic-from-mf-amalgam-trace
kind: route
title: An MF canonical trace on the Kun-Thom double makes an already-nonsofic group hyperlinear
target: hyperlinear-nonsofic-group
requires:
  - reduced-amalgam-canonical-trace-is-mf
  - kt-pair-group-double-is-nonsofic
artifacts:
  - research/artifacts/hyperlinear-firewall-dossier-2026-08-24.md
---

Suppose the canonical trace `tau` on `C*(D)`, `D = G *_Gamma G`, is an MF
trace in the sense of `(RAT1)`.  Then `(C*(D), tau)` embeds into the tracial
matrix ultraproduct along the maps `phi_n`: asymptotic multiplicativity
makes the induced map a `*`-homomorphism, and `tr_(d_n) o phi_n -> tau`
makes it trace preserving, hence injective on the GNS quotient.  Therefore

```text
L(D) = pi_tau(C*(D))''
```

is Connes embeddable, and a group is hyperlinear exactly when its group von
Neumann algebra embeds into `R^omega`.  So `D` is hyperlinear.

Version 3 of Kun--Thom Theorem A, imported as `kt-pair-group-double-is-nonsofic`,
says the group double of an infranormal Kazhdan pair is **not sofic**.
Together, `D` is an explicit hyperlinear nonsofic group: the separation
answer to Pestov Question 3.4.

## What this route costs, stated plainly

The first prerequisite is strictly **stronger** than the conclusion "`D` is
hyperlinear" -- MF trace implies hyperlinear trace implies Connes
embeddability -- so this route does not reduce the problem, it strengthens
the hypothesis.  It is recorded for two reasons that a weaker framing would
lose.

* The strengthening is where the machinery is.  Shulman's Theorem 10 already
  establishes the **algebra-level** statement for every symmetric double of a
  countable residually finite group (`symmetric-double-weak-mf`), so the
  remaining increment is trace selection on top of a theorem that is done,
  rather than a construction from nothing.  The merely-hyperlinear framing
  has no such machine and is a restatement of the target
  (`reduced-amalgam-canonical-trace-is-mf`, Attempt 3).
* Nothing else in the graph consumes `kt-pair-group-double-is-nonsofic`.  The
  existing routes into this root -- `flexible-side-witness`,
  `separation-from-nonsofic-hyperlinear-wreath`, `radical-collision-route` --
  all pair hyperlinearity with a *wreath* nonsoficity claim.  This edge is
  what makes the 2026-08-22 group-double import usable on the flexible side.

The route is therefore honest about being an uphill edge: it names the single
operator-algebraic increment separating an established theorem from a program
answer, and its prerequisite carries the recorded reason (the norm/HS
rank-one separation) that the increment is not formal.
