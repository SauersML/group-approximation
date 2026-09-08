---
rg: 2
id: truncated-charge-induction-forces-a-bounded-creation-witness
kind: route
title: Truncate charge induction at the missing-output bound and extract an expanding component
target: strict-encoders-create-particles-in-a-bounded-cluster
requires:
  - relative-equality-piecewise-injections-are-surjective
  - local-decoders-bound-connected-missing-particle-witnesses
---

We truncate the method of
`charge-level-induction-and-colored-collision-corners`, rather than
substituting a weaker hypothesis into its untruncated conclusion.
The first prerequisite supplies the collision-program implication
needed at each level. Write |x| for particle count and assume initially that

    |tau(x)| <= |x| whenever x is finite and |x|<=K.       (BPC1)

The identity sigma tau=id makes tau injective on finite configurations.
We prove that tau preserves and attains each particle sector n<=K.
The zero sector is immediate. Suppose all smaller sectors have already
been preserved and attained. A charge-n configuration cannot map to a
lower sector: that image already has a preimage of smaller charge,
contradicting injectivity. Thus (BPC1) gives preservation at level n.

Now apply the fixed-level matching construction of the cited charge
induction with every nonzero charge and token weight equal to one.
Every input component and every truncated input
used by Hall's inequality has at most n particles. Its conservation
has therefore just been proved. Stabilizer equality uses only finite
injectivity; there are finitely many component types because n is
fixed. The ordered n-particle map is an injective piecewise coordinate
translation, so the first prerequisite makes it onto. This
attains level n and completes induction through K. No step uses (BPC1)
for larger inputs.

If tau were nonsurjective, the second prerequisite would give a
missing finite configuration with at most |MS|=K particles, contrary
to the sectors just attained. Hence (BPC1) implies surjectivity.
Its contrapositive supplies a finite x with |x|<=K and |tau(x)|>|x|.

Decompose supp(x) into E-components, E=M^(-1)M. A translated memory
gM cannot meet two components: any two sites in gM have relative
displacement in E. Each component therefore evolves independently.
Their output supports are disjoint, since a nonzero output must read
at least one occupied input and no memory can meet two components.
Particle counts of the component outputs consequently add to |tau(x)|.
Since |tau(x)|>|x|, some component c satisfies |tau(c)|>|c|. It has
between one and K sites and is E-connected.

Choose one site p in c. Every other site is reached from p by an
E-edge path of length at most |c|-1, using a spanning tree. Translating
by p^(-1) gives support containing 1_G and contained in E^(K-1).
Equivariance preserves the strict increase. The set E is finite, so
the resulting candidate family is finite. This proves the claim.
