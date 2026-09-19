---
rg: 2
id: minimal-s3-one-letter-actors-have-twisted-countermodels
kind: claim
title: Minimal one-letter S3 actors have finite or amenable twisted countermodels
distinct_from:
  finite-s3-cross-edge-holonomy-cannot-renew-saturated-escape: That assumes the residual multiplicity holonomy factors through a finite quotient; this allows an infinite holonomy group and fences virtually free or amenable active stabilizers.
  agent-aggregate-escape-finite-packet-actor-no-go: That orbit-sums an unconstrained finite packet action; this retains all relations of an infinite one-letter actor by passing to its finite central Schur extension.
  reusable-s3-renewal-is-twisted-radical-or-proper-corner: That classifies what a successful indefinite recurrence would imply; this gives explicit exact or asymptotic countermodels for the smallest candidate presentations.
---

**ESTABLISHED INFINITE-HOLONOMY FIREWALL.**  Let a finite packet carry the
complete outer `S_3` action, let `sigma` be one active packet type, and let
`A_sigma<=S_3` be its stabilizer.  The two smallest presentations obtained by
adding one possible renewal letter are

```text
Q_com=<r,s,u |
       r^2=s^3=(rs)^2=1, [u,r]=[u,s]=1> = S_3 x Z,     (MST1)

Q_free=<r,s,u | r^2=s^3=(rs)^2=1> = S_3 * Z.          (MST2)
```

In both cases let the packet action send `u` to the identity outer
automorphism.  The active stabilizers are

```text
(Q_com)_sigma=A_sigma x Z,
(Q_free)_sigma=preimage_(Q_free -> S_3)(A_sigma).       (MST3)
```

The first is virtually cyclic and the second is virtually free.  For the
finite-valued packet multiplier `omega`, both inverse twisted stabilizers
have nonzero finite-dimensional star representations satisfying every actor
relation.  Tensoring with the packet implementers and inducing over the
finite type orbit gives an exact finite-dimensional full-cell representation
with positive `sigma` density.  Hence neither `(MST1)` nor `(MST2)` can renew
the saturated `S_3` escape, regardless of how the free multiplicity unitary
is chosen.

The same exact countermodel applies to every actor which is a finite graph of
finite packet groups, including any one-stable-letter HNN extension over
finite packet subgroups.  Its active stabilizer is virtually free.  The
finite Schur central extension associated to `omega` is again virtually free
and residually finite.  A finite quotient which retains its central phase
has a regular representation whose required central-character block is a
nonzero inverse-projective finite-dimensional stabilizer representation.

There is a broader approximate fence.  If the active stabilizer `Q_sigma` is
amenable, then every scalar twisted regular algebra

```text
L_(omega^(-1))(Q_sigma)                                 (MST4)
```

is hyperfinite and has matrix microstates.  Tensoring those microstates with
the fixed packet implementers and inducing over the finite type orbit gives
full-cell microstates with relator energy tending to zero and active density
bounded below.  Consequently no dimension-uniform indefinitely reusable
supercritical recurrence can hold for an amenable stabilizer.  This fences,
for example, `S_3` coupled to an infinite cyclic, abelian, solvable
Baumslag--Solitar, or other amenable multiplicity clock, even when its
holonomy does not factor through a fixed finite quotient.

Thus the smallest one-letter presentations do not realize reusable
automorphic renewal.  A surviving automorphic actor must have a nonamenable
active stabilizer whose inverse twisted regular trace itself has no matrix
microstates; adding a free, commuting, finite-edge HNN, or amenable compressor
letter cannot provide the recurrence.

The first property-`(T)` audit is now separated cleanly by
`s3-packet-dressing-preserves-projective-microstate-gap`.  Thom's nonamenable
LEF Kazhdan central fibre still has projective regular microstates, and fixed
packet tensoring plus finite-orbit induction preserves them at positive
density.  Requiring finite presentation points to Deligne's triple cover,
but the resulting `S_3` packet cell has a uniform HS gap if and only if the
bare mod-three Maslov projective sector does.  Hence nonamenability and
property `(T)` move the problem beyond amenable absorption but do not let the
finite packet manufacture the missing radical.

DERIVATION
minimal-s3-one-letter-twisted-countermodel-proof
