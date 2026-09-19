---
rg: 2
id: finite-cyclic-actor-root-kernel-dichotomy
kind: claim
title: A finite cyclic payload actor either kills perfect completeness or retains the root-kernel countermodel
distinct_from:
  split-steinberg-conditional-swap-has-root-kernel-countermodel: that kills an unattached split Steinberg root system; this includes the smallest load-bearing cyclic amalgam and its exact conditional antiphase row.
  binary-tetrahedral-conditional-e5-root-bridge: that uses a finite cyclic root packet to detect a nontrivial root central character; this shows why such a packet cannot by itself detect whether the root came from the prescribed payload coefficient.
  one-letter-reynolds-rows-globalize-structurally: that treats subgroup conjugacy by one HNN letter; this treats finite actors amalgamated to the conditional Whitehead word.
---

**ESTABLISHED FINITE-ACTOR DICHOTOMY.**  Let

```text
p=B_f,   W=x_12(p)x_21(-p)x_12(p),
z=diag(1,-1).                                           (FCA1)
```

In every genuine coefficient representation,

```text
W^4=1,          W z W^(-1)=W^2 z,
W diag(p,0)W^*=diag(0,p).                              (FCA2)
```

The middle identity follows because `W=1` on `1-p`, while on `p` it is the
quarter-turn `[[0,1],[-1,0]]`.  Thus the apparently ideal smallest actor is
the finite dihedral packet

```text
D8=<u,z | u^4=z^2=1, u z u^(-1)=u^2 z>,
u=W.                                                    (FCA3)
```

It is load-bearing only superficially.  Killing every Steinberg root and
`u` leaves the quotient `D8/normalClosure(u)=<z>~=C_2`.  Hence the external
structural packet, the marked involution, and the grading survive.  Pulling
back the finite uniform-assignment/role model gives

```text
tau(QB_f)>0,       rho(W)=rho(u)=1,
rho(W)QB_f rho(W)^*=QB_f,                              (FCA4)
```

with zero defining-relator defect.  The exact antiphase law `(FCA2)` therefore
does not imply any payload detection or overlap loss.

The same argument gives a sharp dichotomy for every finite cyclic actor in
this syntax.  Let `A` be a finite actor with distinguished finite-order
element `u`, amalgamate `u=W`, and suppose its only overlap with the outer
BCS/role system is a finite **central protected-sign group** `Z`.  Fix the
protected character `chi` carrying the marked perfect seed.  Put

```text
Abar=A/normalClosure(u).                                (FCA5)
```

Because `p=0` in the perfect trace, the coefficient word has `W=1` there.
Therefore any exact perfect extension in the `chi` sector factors through a
unitary representation of `Abar` whose restriction to `Z` is `chi`.

There are now only two cases.

1. `Abar` has no `chi` representation.  Then the proposed actor cannot extend
   the marked perfect model, so completeness fails.
2. `Abar` has a `chi` representation.  Since `Abar` is finite, take it finite
   dimensional.  Tensor/amplify it with the exact finite uniform-assignment
   structural model in the same central `chi` sector.  Kill every root and
   send `A` through `Abar`.  All amalgam and actor relations hold exactly,
   the mark and seed survive, `B_f` has positive trace, and `W=1`.  Hence the
   desired HS escape inequality fails already in an exact finite model.

Thus no finite-order relation, cyclic amalgam, or finite conditional grading
actor attached only through central protected signs can destroy the
root-kernel quotient while preserving perfect completeness.  Extra finite
Clifford phases do not change the dichotomy; they are part of `A` and survive
or die in `(FCA5)`.

The boundary is precise.  A surviving attachment must share **noncentral
payload structure** with the actor, so that the perfect and uniform-positive
restrictions cannot be exchanged merely by keeping the same protected
character.  But authenticating that noncentral restriction is exactly the
root-to-payload/groupification gate; a central cyclic packet does not solve
it.

DERIVATION
conditional-dihedral-actor-root-kernel-proof
