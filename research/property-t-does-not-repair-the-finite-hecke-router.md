---
rg: 2
id: property-t-does-not-repair-the-finite-hecke-router
kind: claim
title: Property (T) does not repair a finite Hecke router: SL3(Z) has exact congruence absorbers
artifacts:
  - research/property-t-sl3-congruence-hecke-absorber-proof.md
distinct_from:
  single-nonreducing-hecke-transport-cannot-carry-a-complete-context: that proves the universal one-compression rank obstruction and a finite S4 absorber; this embeds the same packet in a property-(T) actor and preserves it in an infinite congruence family.
  property-t-fixed-holonomy-character-regularization: that controls a fixed holonomy after character regularization; here exact representations retain macroscopic off-corner holonomy.
  strict-compressor-exact-actor-collapse: that uses an infinite subgroup inclusion; here the anchor is finite and congruence quotients preserve its nonnormal relative position.
---

The property-(T) group SL_3(Z) contains the rotational signed-permutation
subgroup
```text
O_3(Z)^+ isomorphic to S_4.
```
Inside this subgroup choose
```text
E isomorphic to D_8,       J in Z(E),       a in E,
t a t^-1=J,                t J t^-1=a.
```
For
```text
q=(1-J)/2,        p_+=q(1+a)/2,        p_-=q(1-a)/2,
```
the nonnormal Hecke packet satisfies
```text
q t p_+ t^-1 q=0,
q t p_- t^-1 q=p_-,
q t q t^-1 q=p_-.                                      (PTH1)
```

For every odd prime ell, reduction to SL_3(F_ell) is injective on this
S_4.  In the finite quotient's left regular representation,
```text
tau(q)=1/2,             tau(p_+)=tau(p_-)=1/4,
||(1-q)t^*q||_2^2=1/4.                                  (PTH2)
```
The infinite left regular representation of SL_3(Z) has exactly the same
values.  Thus property (T), residual finiteness, and a nonnormal finite
anchor coexist with an infinite family of exact finite absorbers.

In particular property (T) supplies no estimate shrinking the named
off-corner block.  Kazhdan rigidity can be invoked only after separate
rows make q nearly invariant under a Kazhdan generating set.  Making it
invariant under the transporter returns to the reducing normalizer case.

Therefore replacing the virtually free minimal host by a familiar
property-(T) congruence actor does not advance the compiler.  The needed
infinite host must have a matrix-specific stability theorem that controls
the selected off-corner block and must simultaneously avoid a congruence
family preserving the finite Hecke packet.  Property (T) by itself is
strictly insufficient.
