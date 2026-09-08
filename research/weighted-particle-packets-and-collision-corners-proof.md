---
rg: 2
id: weighted-particle-packets-and-collision-corners-proof
kind: route
title: Encode positive integer charge by colored packets, lift weighted Hall matchings, and rationalize conserved real charges
target: finite-injective-positive-charge-automata-are-surjective
requires:
  - relative-equality-piecewise-injections-are-surjective
---

## Complete token packets form a finitely defined domain

First suppose every w(a) is an integer. If A={0}, the configuration
space is a singleton and the conclusion is immediate. Otherwise define
the finite token-color set

    C={(a,j) : a in A minus {0}, 1<=j<=w(a)}.

A finite configuration x is encoded by the token set

    P_x={(g,(a,j)) : x(g)=a!=0, 1<=j<=w(a)}.

The number of its tokens is its total charge. Fix N>=1. An ordered
encoding of a configuration of charge N is an element of

    C^N x G^N

whose tokens are distinct and, at every occupied position, have colors
exactly (a,1),...,(a,w(a)) for one a. Positions may repeat; the full
position-color pairs may not. Write V_N for this valid domain.

Validity is defined by a finite Boolean combination of color conditions
and coordinate equalities g_i=g_j. Indeed, the equality partition of the
N coordinate indices identifies each occupied site, and the colors in
that block must be exactly one complete packet. Thus V_N is a definable
domain of the finite-control relative-equality calculus in the required
claim. No injectivity assumption is imposed on the position tuple alone.

## Components have finitely many labeled types at fixed charge

Choose a finite memory M for tau containing 1_G. Join occupied input
positions p,q if p^(-1)q belongs to E=M^(-1)M. Distinct components
cannot meet one translated output neighborhood gM. Since tau fixes 0,
the output of a configuration is the union of the outputs of its
components, with disjoint output supports. Conservation preserves the
total charge of each component separately.

At charge N there are at most N occupied positions, because every
nonzero symbol has integer charge at least 1. Rooting an E-connected
component at one of its sites places its support in E^(N-1). The
alphabet is finite, so only finitely many translation types of labeled
components of charge at most N occur.

## Weighted Hall matchings respect finite stabilizers

Fix one labeled component x and let y=tau(x). Consider the finite
bipartite graph from output tokens (q,c') in P_y to input tokens (p,c)
in P_x, with an edge whenever p is in qM. Token colors do not restrict
these edges.

For any subset Z of output tokens let U be its set of positions.
Truncate x to UM, obtaining x_U. Its output agrees with y on U,
because every memory qM for q in U is contained in UM. The output
therefore contains every token of Z. By conservation, the number of
input tokens of x_U is the total output charge of x_U and is at least
|Z|. Those input tokens are exactly the neighbors of Z. Hall's theorem
supplies a matching of all output tokens. Since total input and output
charges are equal, it is a perfect matching.

Let H be the translation stabilizer of x. It is finite since x has
finite nonempty support, and it acts freely on tokens: a group element
fixing a token's position is the identity. Equivariance gives H subset
Stab(y), and injectivity on finite configurations gives equality.
The bipartite graph is H-invariant.

Apply Hall's inequality to unions of H-orbits of output tokens. Every
input and output orbit has |H| elements, so dividing by |H| gives
Hall's condition for the quotient graph. A quotient perfect matching
lifts to an H-equivariant perfect matching: choose one adjacent pair
in each matched pair of orbits and translate it by every h in H.
Every matched input position p and output position q satisfy
q=p d for some d in M^(-1), although their token colors may differ.

Choose such a matching for each of the finitely many labeled component
types at charge at most N, and translate it equivariantly. Stabilizer
equivariance makes the transported choice independent of the translator.
For a whole configuration, take the union of its component matchings.

## Ordered token lifts lie in the finite-control collision calculus

Apply the chosen matching to each token of an ordered valid tuple in
V_N. The output is an ordered token encoding of tau(x), hence lies
in V_N. It is injective: equality of ordered outputs implies equality
of the output configurations. Finite-configuration injectivity gives
the same input configuration, and the fixed matching on that configuration
is a bijection of its token set, recovering the input ordering.

The lift has finitely many possible simultaneous position displacements,
each in (M^(-1))^N, and finitely many possible output color tuples.
Each branch is selected by finitely many relative-coordinate equality
tests and colors. To see this explicitly, pairwise tests against E
find the token's occupied-site component. Its rooted support is then
identified by tests against E^(N-1), and its state labels and token
indices are read from the finite color tuple. This finite rooted data
determines the selected component matching, including the output token
color and displacement. Repeated positions belonging to one packet
cause no ambiguity because that packet's token colors are distinct.

Thus the lifted injection is an endomap of the definable domain V_N
of exactly the kind covered by
relative-equality-piecewise-injections-are-surjective. Equivalently,
its linearization belongs to the corner cut out by the valid-packet
projection in a finite matrix algebra over the collision algebra. Its
explicit transpose is a left inverse in that corner; stable finiteness
forces a right inverse as well. The required claim therefore makes
the token lift surjective.

Every configuration of charge N has an ordered token encoding. A
preimage for that ordered encoding decodes to a finite x with the
desired output. Hence tau is onto the charge-N sector, and it is
injective there by assumption. The charge-zero sector is the singleton
{0}. This proves bijectivity on every finite sector for integer charges,
including cases where a sector is empty.

## Positive real conservation yields positive integer conservation

Now let w have the stated real values. Set m=|A minus {0}|. For every
finite configuration x let v(x) in Z^m count its occurrences of each
nonzero symbol. Define the rational vector space

    L=span_Q {v(tau(x))-v(x) : x finite} subset Q^m.

Although its generating family may be infinite, L is finite-dimensional
and has a basis of rational vectors. Conservation says that the real
weight vector w lies in the real annihilator L^perp. This annihilator
has a rational basis, so its rational points are dense in its real
points. Since w has every coordinate strictly positive, sufficiently
close rational points also have every coordinate strictly positive.
Choose one and multiply by a common denominator, obtaining a vector
w' of strictly positive integers annihilating L. Set w'(0)=0.

For every finite x, the difference v(tau(x))-v(x) lies in L, so tau
conserves w'. The integer-charge argument therefore supplies a finite
preimage for every finite target. The original real charge w is also
conserved, so this preimage has the same original real charge as its
target. Finite-configuration injectivity then proves bijectivity on
each original real-charge sector as claimed. The argument asserts
existence of w', without assuming an algorithm that computes L.

Finally finite configurations are dense in A^G. The continuous image
of the compact space A^G is closed, so attainment of every finite
configuration implies surjectivity on the entire full shift. No
assumption of global injectivity or a preexisting decoder is needed.
