---
rg: 2
id: leavitt-regular-a5-wreath-is-minimally-almost-periodic
kind: claim
title: The regular A5 wreath over the simple Leavitt actor has no nontrivial finite-dimensional representations
distinct_from:
  simple-lamp-hyperlinear-recovery-forces-action-sofic: That asks for equivariant classicalization of arbitrary HS microstates of a generalized A5 wreath; this proves only the exact finite-dimensional collapse for the regular action of the specific simple Leavitt actor.
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: That exhibits arbitrary exact multiplicity gauges for actors with finite-dimensional representations; this shows that exact gauge obstruction disappears for the Leavitt actor, while genuinely asymptotic gauges remain possible.
  ordinary-leavitt-quotient-fences-whitehead-active-floor: That isolates an ordinary Leavitt quotient behind the Whitehead active profile; this uses the already established characteristic-two simple nonsofic Leavitt group as an actor in a separate lamp compiler.
---

**ESTABLISHED.**  Put

```text
Q=EL_4(L_(F_2)(1,2)),
W=(directSum_Q A5) semidirect Q,                         (LRW1)
```

where `Q` acts on its own index set by left translation.  Then every
finite-dimensional unitary representation of `W` is trivial.  In
particular `W` is finitely generated, nontrivial, minimally almost periodic,
and nonsofic.

Indeed the established Leavitt central-cover rigidity implies that `Q` is
infinite simple and nonsofic.  If

```text
rho:W -> U(d)
```

is a homomorphism, then `rho|_Q` is trivial.  Otherwise simplicity would make
it faithful, so `Q` would be a finitely generated linear group over `C`.
Malcev residual finiteness would then make `Q` sofic, a contradiction.

For `x in Q`, write `A5_x` for the coordinate lamp.  Actor covariance and
triviality of `rho|_Q` give

```text
rho(A5_x)=rho(A5_(gx))                                  (LRW2)
```

for every `g,x in Q`; transitivity makes all coordinate images equal to one
subgroup `H<=U(d)`.  Distinct coordinate lamps commute.  Hence every two
elements of `H` commute: realize the first from `A5_x` and the second from
`A5_y` with `x!=y`.  Thus the image of each perfect group `A5_x` is abelian
and therefore trivial.  The lamps and actor generate `W`, proving the
claim.  Finite generation uses a finite generating set of `Q` and two
generators of the base-site `A5`; actor conjugation supplies every site.
Finally `Q<W`, so nonsoficity of `Q` implies nonsoficity of `W`.

This removes one nuisance from the simple-lamp recovery route, but not its
normalized-HS gate.  An **exact** multiplicity-fiber representation of the
Leavitt actor is forced to be trivial.  If `Q` is hyperlinear, however, its
canonical microstates are nontrivial asymptotic representations and can live
entirely in a lamp-commutant multiplicity fiber.  Thus exact minimal almost
periodicity does not yield the required equivariant multiplicity
classicalization.  A dimension-uniform correction of that asymptotic fiber
would already make either `Q` or `W` nonhyperlinear.

DERIVATION
leavitt-regular-a5-wreath-map-proof
