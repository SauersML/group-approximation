---
rg: 2
id: raw-core-central-reynolds-authentication-is-circular
kind: claim
title: Central Reynolds projections do not authenticate a moving endpoint fiber from the raw BS core
distinct_from:
  authenticated-core-union-basin-is-relative-liftability: that identifies the full positive endpoint as relative ultraproduct liftability; this audits the proposed central-idempotent construction and proves exactly where it presupposes that lift.
  bs14-bounded-moments-cannot-extract-congruence-level: that shows fixed finite moment tests cannot distinguish deep regular congruence levels; this also treats conductor-dependent central idempotents and the ambiguity among endpoint types with one identical core.
  cyclic-core-character-forces-linear-rms-section-area: that gives the quantitative frozen-section lower bound; this applies it to rule out direct evaluation of endpoint Reynolds projections on a raw almost-endpoint tuple.
---

**ESTABLISHED METHOD FIREWALL; NOT A COUNTEREXAMPLE TO FLEXIBLE
LIFTABILITY.**  Let `(R,T)` be an exact finite-dimensional square-free
`BS(1,4)` core and let `X` have small endpoint relator energy.  A construction
of the missing endpoint type by finite-quotient central idempotents cannot
proceed in either of the following two literal ways:

1. choose the endpoint atom from the exact core algebra and then use its
   Reynolds projection;
2. evaluate the full endpoint central idempotents on `(X,R,T)` through an
   arbitrary word section with a dimension- and level-independent error
   bound.

The first method is algebraically nonidentifiable, and the second is
quantitatively nonuniform.  Passing both barriers is already the relative
lifting theorem in `authenticated-core-union-basin-is-relative-liftability`.

## The level is known, but the endpoint atom is not

There is no separate unknown-conductor problem.  Put

```text
N=ord(T).                                               (RCR1)
```

Every exact endpoint over this literal core factors through the one finite
quotient

```text
A_N=A/normal_closure(t^N),                              (RCR2)
```

by `one-core-endpoint-union-is-one-finite-restriction-fiber`.  Thus all
candidate central idempotents live in the known finite algebra `C[A_N]`.

Nevertheless the restriction `C[A_N]->C[B_N]` does not identify which
endpoint central summands occur.  The exact tuples in
`cuspidal-redistribution-refutes-regular-core-orbit-basin` have, after one
unitary alignment,

```text
rho_p|B=eta_p|B                                      (RCR3)
```

while their global cuspidal multiplicity profiles differ on asymptotic
density `1/2`.  Every operator built only from `(R,T)` is therefore identical
on these two models, although the endpoint central idempotents have different
ranks.  Hence no core-algebra Reynolds projection can select the adaptive
nonnegative restriction-fiber point.  This remains true with an exactly
regular authenticated core and asymptotically regular global character.

## Full central idempotents already require an endpoint lift

For a central idempotent

```text
z_lambda=(dim lambda/|A_N|)
          sum_(g in A_N) conjugate(chi_lambda(g)) g,    (RCR4)
```

evaluation on an exact representation is canonical.  On the raw generator
tuple it is not: one must first choose words `w_g(X,R,T)` for every `g`, and
different words agree only after filling endpoint relators.  A uniform
Reynolds estimate would therefore require a uniform section-energy bound
turning the short presentation residual into approximate multiplication of
the whole table `(w_g)`.

That frozen-core estimate is false.  The scalar core-character family in
`cyclic-core-character-forces-linear-rms-section-area` has exact core,
endpoint energy `O(K^(-2))`, and constant section edge energy for **every**
section of `A_(4^K-1)/B_(4^K-1)`.  Equivalently, its RMS section filling cost
is at least `cK`.  Therefore direct word evaluation of `(RCR4)` cannot have a
dimension- and level-independent Lipschitz bound while the supplied core is
held fixed.

Moving the core before evaluating `(RCR4)` removes that scalar family, but
this is precisely the minimization in
`gauge-optimized-section-energy-controls-flexible-repair`; it is not an
independent Reynolds shortcut.  Likewise, bounded word/moment substitutes
cannot help, because `bs14-bounded-moments-cannot-extract-congruence-level`
shows that every fixed finite family is blind to distinct sufficiently deep
regular congruence models.

## Exact endpoint authentication is sufficient and is the missing theorem

If a compatible endpoint type and an approximate endpoint intertwiner have
already been produced, then
`congruence-cross-type-mixing-has-uniform-polar-repair` averages it in the
common finite quotient and repairs arbitrary multiplicity mixing with
discarded/padded rank `O(E d)`.  Central Reynolds averaging is fully uniform
at that stage.

Thus there is no residual polar, cross-stratum, or finite-group stability
problem after authentication.  But producing the input to that averaging
from `(X,R,T)` is exactly a coordinate lift of the relative ultraproduct
homomorphism.  The central-idempotent formula `(RCR4)` presupposes the
approximate multiplication table whose construction is the desired lift.
It therefore cannot prove the lift without a new gauge-optimized
two-dimensional/section theorem.

This claim rules out the proposed direct central-Reynolds route.  It does
not show that adaptive moving-fiber authentication is false, and it supplies
no nonhyperlinear group by itself.
