---
rg: 2
id: simple-lamp-gauge-rigidity-reduces-to-actor-classicalization
kind: claim
title: Joint simple-lamp gauge rigidity contains hyperlinear-to-sofic classicalization of the Kazhdan actor
distinct_from:
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that gives the one-automorphism exact Fourier fiber; this audits all actor products and canonical actor traces jointly.
  simple-lamp-hyperlinear-recovery-forces-action-sofic: that is the desired global implication for the Kun-Thom action; this identifies what a proof based only on the commutant gauges would additionally have to establish.
  all-abelian-uniform-hs-rounding-gives-global-pvm: that uniformly rounds an amenable abelian group; the actor here is a nonamenable Kazhdan group and the needed conclusion is monomial/permutation classicalization.
---

ESTABLISHED AS A REDUCTION.  After a finite `A5^F` lamp packet has been
classicalized, write an actor normalizer as

```text
U_g=(P_(alpha_g) tensor 1) C_g,                           (SGR1)
```

where `C_g` lies in the right-regular/multiplicity commutant.  Actor
multiplication says precisely that `(C_g)` is an approximate unitary cocycle
for the induced action on that commutant.  In particular the special family

```text
C_g=1 tensor v_g                                          (SGR2)
```

is allowed for every normalized-HS approximate representation `v` of the
actor.  Lamp covariance is exact, while actor product defect and canonical
trace constraints are exactly those of `v` (up to the harmless permutation
factor in `(SGR1)`).

Consequently, a theorem which uses only

1. the complete Kazhdan actor relations,
2. canonical actor trace tests, and
3. exact/approximate normalization of the regular simple-lamp packet,

to make all `C_g` jointly monomial would also have to classicalize arbitrary
canonical hyperlinear approximations carried in `(SGR2)`.  For the
Kun--Thom actor this is a nonamenable property-`(T)` hyperlinear-to-sofic
approximation-rigidity problem; the amenable-base theorem does not apply.

There is no counterexample from a fixed finite-dimensional actor twist.  If
`sigma` is a free permutation approximation and `pi` is a fixed
finite-dimensional representation, then

```text
P_(sigma(g)) tensor pi(g)                                 (SGR3)
```

is locally untwisted on every free orbit by the basis change

```text
delta_h tensor xi  |->  delta_h tensor pi(h)^(-1) xi.     (SGR4)
```

For an exact regular finite quotient this gives the familiar identity
`lambda tensor pi ~= lambda^(dim pi)`.  Thus property `(T)` permitting
nonmonomial finite-dimensional representations does not itself refute joint
classicalization; the regular multiplicity absorbs them.

The sharp verdict is therefore:

- one-normalizer recovery is false by the Fourier fiber;
- fixed representation-valued gauge counterexamples disappear by regular
  absorption;
- a full positive theorem needs a new result that every gauge approximation
  arising in the Kun--Thom microstates is sofic-induced/monomializable after
  a commutant conjugacy.

No such theorem is currently available for this nonamenable Kazhdan actor.
Hence finite simplicity plus the Kazhdan family does not yet close the
multiplicity-copy action; it relocates the gate to actor approximation
classicalization.

## Attempts

- **Use a fixed nonmonomial finite quotient representation.**  Tensoring it
  with the free permutation part makes it regular-absorbed by `(SGR4)`.
- **Use property `(T)` on the cocycle.**  Ordinary property `(T)` controls
  almost-invariant Hilbert vectors, not arbitrary exact unitary
  representation-valued cocycles in a matrix commutant.
- **Use canonical actor traces.**  They can be supplied entirely by the
  independent factor `v_g` in `(SGR2)` and do not couple it to lamp sites.
- **Apply amenable classicalization again.**  The lamp base is amenable, but
  the actor and its Kazhdan stabilizer are not; this is exactly outside the
  theorem's hypothesis.
