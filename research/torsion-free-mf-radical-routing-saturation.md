---
rg: 2
id: torsion-free-mf-radical-routing-saturation
kind: claim
title: Routing one MF-radical word onto a torsion-free quotient forces hereditary full radical
artifacts:
  - research/torsion-free-mf-routing-saturation-proof.md
distinct_from:
  acylindrical-hyperlinear-saturation-compiler: that starts from an operator-to-Hilbert--Schmidt shadow and uses Property T in the analytic transfer; this starts from actual MF-radical membership and uses only functoriality and normal generation.
  two-generated-single-element-hull-router: that supplies a paper-level small-cancellation quotient; this is the algebraic MF-radical consequence of any supplied routing data and contains no small-cancellation or literature input.
---

**ESTABLISHED, WITH NO PROPERTY `(T)`.**  Let `E,Q` be countable groups,
let `q:E->>Q` be surjective, and let `d in E` satisfy

```text
d in Rad_MF(E),                 q(d)!=1,
normalClosure_Q(q(d))=Q.                                  (TFR1)
```

Then

```text
Rad_MF(Q)=Q,                                             (TFR2)
```

and every nontrivial quotient of `Q` also has full MF radical.  If the
supplied routing data additionally say that `Q` is two-generated, finitely
presented, torsion-free, and acylindrically hyperbolic, all those properties
are retained in the conclusion.

This is the complete approximation-theoretic saturation step needed by the
torsion-free manuscript theorem.  It uses neither a Kazhdan subgroup nor an
operator-to-Hilbert--Schmidt conversion.  The remaining obligations are to
produce an intrinsically torsion-free marked seed `(E,d)` satisfying actual
MF-radical membership and to construct the routing quotient internally.

**Why the torsion-free `Q` has to be supplied and cannot be manufactured
(2026-09-08).**  `(TFR1)` takes the routing quotient as data, and that is not a
presentational convenience.  By
`full-mf-radical-seed-has-no-torsion-free-quotient` there is a finitely
presented full-MF-radical group whose only torsion-free quotient is trivial, so
no procedure valid on every full-MF-radical input can produce the `Q` of
`(TFR1)` as a quotient of the input.  The recorded obligation to construct the
routing quotient internally is therefore an obligation about this construction
specifically, not an instance of a general principle waiting to be found.

DERIVATION
torsion-free-mf-routing-saturation-proof
