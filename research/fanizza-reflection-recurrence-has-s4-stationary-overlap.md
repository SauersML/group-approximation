---
rg: 2
id: fanizza-reflection-recurrence-has-s4-stationary-overlap
kind: claim
title: The ordinary-word shadow of Fanizza doubling has an exact S4 stationary-overlap model
distinct_from:
  fanizza-doubling-carriers-form-orthogonal-flag: that identifies the reflection word carried by an exact orthogonal projection recurrence and isolates the forgotten overlap; this supplies a smallest exact finite group model in which the reflection word holds while that overlap is positive.
  flat-fanizza-triangle-realizes-every-separator-distribution: that gives diagonal models of the abstract context tables; this is a nonabelian prescribed-word model of the actual one-step reflection recurrence.
---

Let

```text
V=<d,e>=(C_2)^2
```

and let `x,u in GL(V)=GL_2(F_2)` act by

```text
x:d |-> e, e |-> d,
u:d |-> de, e |-> e.                                  (SFO1)
```

Both `x` and `u` are involutions and they generate `GL_2(F_2)`.  Hence

```text
K=V semidirect <x,u> = AGL_2(F_2) ~= S_4.              (SFO2)
```

In `K` one has the literal ordinary group-word identity

```text
u d u^(-1)=de=d (x d x^(-1)).                          (SFO3)
```

Put, in the group algebra,

```text
P=(1-d)/2,
R=xPx^(-1)=(1-e)/2,
P'=uPu^(-1)=(1-de)/2.                                  (SFO4)
```

The three involutions `d,e,de` commute.  Thus `(SFO3)` is exactly the
reflection-word shadow

```text
1-2P'=(1-2P)(1-2R).                                    (SFO5)
```

But in the regular trace of `K`,

```text
tau(P)=tau(R)=tau(P')=1/2,
tau(PR)=1/4,                                           (SFO6)
```

and direct expansion gives

```text
P+R-P'=2PR,
||P+R-P'||_2^2=4 tau(PR)=1.                            (SFO7)
```

Consequently the word recurrence is exact while the additive doubling
recurrence fails by a full normalized-Hilbert--Schmidt unit.  Conjugating
`(SFO3)` by powers of `u` gives the same exact stationary model at every
virtual level.  Direct sums and tensor products give it in arbitrary
multiplicity.

This is the precise stationary gauge erased when

```text
P_n+X_nP_nX_n=P_(n+1)
```

is replaced by

```text
Z_(n+1)=Z_n X_n Z_n X_n^(-1).
```

The former says that two cuts are orthogonal and their union is the next
cut.  The latter records only their symmetric difference.  The hidden
intersection is `PR`, and `(SFO6)` shows that finite-dimensional rank can
park exactly half of the source carrier there.

Tensoring this model with an independent negative-central-character D8
packet leaves the D8 holonomy projection positive and changes none of the
word identities.  Therefore neither the Fanizza reflection recurrence nor
its arbitrarily many conjugate copies can supply either proper return in
`single-triangle-trace-cyclic-return-cell`.  A successful actuator must use
the nonlinear guarded C18 relation to charge the overlap, not merely its
ordinary reflection-word consequence.
