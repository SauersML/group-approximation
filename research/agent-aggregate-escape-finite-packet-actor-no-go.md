---
rg: 2
id: agent-aggregate-escape-finite-packet-actor-no-go
kind: claim
title: Every actor action on a fixed finite packet has an exact marked orbit-sum countermodel
distinct_from:
  packet-kazhdan-commutant-placement-decouples: that treats an actor commuting with an independent packet tensor factor; this allows a genuinely nontrivial automorphism action on the packet and still constructs a finite-dimensional covariant extension.
  kazhdan-and-transverse-packets-cannot-orient-clifford-twist: that leaves an arbitrary amplified multiplicity sign inside one covariant representation; this proves extension existence for every packet representation after a bounded orbit sum, independently of property T.
  agent-aggregate-escape-rfd-support-orientation-firewall: that states the fd-radical condition for ACO4; this supplies the exact finite-dimensional representation violating it for every finite-packet semidirect actor.
---

**ESTABLISHED ACTOR NO-GO.**  Let `F` be a fixed finite packet and let an
arbitrary group `L` act by automorphisms

```text
alpha:L -> Aut(F).
```

Every finite-dimensional representation `sigma` of `F` extends, after an
amplification of factor at most `|Aut(F)|`, to a finite-dimensional
representation of the semidirect product `F semidirect L` whose restriction
to `F` contains `sigma`.

Indeed the image `H=alpha(L)` is finite.  Sum the finite `H`-orbit of
`sigma` and let `H` permute the orbit summands with the canonical
intertwiners.  This is a covariant representation of `F semidirect H`, and
inflating it along `L->H` gives the required representation of
`F semidirect L`.

Consequently, suppose `K` is a central packet sign fixed by the action and
some forbidden marked corner `T e_i`, `T=(1-K)/2`, is nonzero in a packet
representation.  The orbit-sum extension still has

```text
sum_j ||T e_j||_2^2>0                                  (AOS1)
```

whenever the actor permutes the finite forbidden menu (and in particular
when it fixes `e_i`).  All actor relations and covariance rows have zero
defect.  Hence no nonamenable, property-`(T)`, simple, or finite-bi-index
actor can prove `(ACO4)` merely by acting through automorphisms of a fixed
finite context/Schur/role packet.

This conclusion does not depend on finite quotients of `L`: the finite image
is forced by finiteness of `Aut(F)` and is already a quotient supplied by the
chosen action.  If `L` has no nontrivial finite quotient, the action itself
is trivial and the construction reduces to the spectator tensor model.

The only surviving actor coupling must therefore be representation-size
dependent or act on an infinite coefficient object whose finite windows do
not close under one bounded orbit sum.  Equivalently, it must cease to be a
fixed finite-packet covariance attachment and must provide the HS-radical
modulus `(RF4)` directly.

DERIVATION
agent-aggregate-escape-finite-packet-actor-no-go via agent-aggregate-escape-finite-packet-actor-no-go-proof
