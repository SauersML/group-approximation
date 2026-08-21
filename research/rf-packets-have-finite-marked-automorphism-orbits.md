---
rg: 2
id: rf-packets-have-finite-marked-automorphism-orbits
kind: claim
title: Residually finite packets always have a finite marked automorphism orbit
distinct_from:
  dyadic-affine-pauli-patterns-have-odd-periodizations: that builds finite odd affine models for each prescribed dyadic site pattern; this gives one finite characteristic quotient which is simultaneously invariant under an arbitrary automorphism actor.
  infinite-schreier-pvm-transport-kills-finite-mark: that collapses finite-support PVM mass on uniformly nonamenable infinite type orbits; this proves that a residually finite packet always has a marked finite orbit on which that theorem cannot act.
  hyperlinear-hs-stable-is-residually-finite: that derives residual finiteness from hyperlinearity and same-dimension HS stability; this shows why residual finiteness makes the proposed automorphism-type recurrence sterile.
---

ESTABLISHED.  Let `Gamma` be finitely generated and residually finite, let
`1!=y in Gamma`, and let a group `B` act on `Gamma` by automorphisms.  There
is a finite characteristic quotient

```text
q:Gamma -> Q                                             (RFA1)
```

such that `q(y)!=1`.

Indeed choose a finite-index normal subgroup `N` not containing `y`, put
`m=[Gamma:N]`, and let `C` be the intersection of every subgroup of `Gamma`
of index at most `m`.  A finitely generated group has only finitely many
subgroups of each fixed index, so `C` has finite index.  It is characteristic
by construction, and `C<=N`; take `Q=Gamma/C`.

Every automorphism in `B` descends to an automorphism of `Q`.  Hence the
semidirect product has a finite marked quotient

```text
Gamma rtimes B -> Q rtimes image(B->Aut(Q)),            (RFA2)
```

and the image of `y` remains nonidentity.  The group on the right is finite
because both `Q` and `Aut(Q)` are finite.

Equivalently, choose an irreducible unitary representation `theta` of `Q`
which does not kill `q(y)`; one exists because the regular representation is
faithful.  The type `theta circ q` has a finite `B`-orbit, contained in the
finite dual of `Q`, and some type in that orbit sees `y` nontrivially.  Thus
no automorphism action on the finite-dimensional type space of `Gamma` can
put **every** `y`-visible type in a uniformly nonamenable infinite Schreier
component.

This rules out the most direct non-fusion continuation of
`kazhdan-type-blocks-pack-a-square-function`: exactify a residually finite
packet, let two or more automorphism routers generate an expanding type
graph, and try to collapse the marked type PVM.  The finite orbit above is an
exact zero-defect reservoir for the mark.  In particular, combining
same-dimension HS stability with a hyperlinear packet cannot evade the
firewall, because `hyperlinear-hs-stable-is-residually-finite` makes that
packet residually finite first.

A surviving type-transition actuator must therefore use a packet with the
mark already in its finite residual, a genuinely proper endomorphism not
descending to one common finite characteristic quotient, or a
finite-matrix-only proper-corner relation.  Automorphisms of an RF packet are
insufficient regardless of how nonamenable their infinite type orbits are.
The first proper-endomorphism candidate is also excluded:
`abelian-matrix-hnns-have-marked-finite-quotients` shows that every finite
family of injective endomorphisms of `Z^n` becomes invertible on one finite
congruence quotient which still detects any prescribed nonzero mark.
