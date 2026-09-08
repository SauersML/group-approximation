---
rg: 2
id: decoder-memory-and-separated-cluster-gluing-proof
kind: route
title: Bound a reverse-identity witness by decoder memory and glue separated preimages
target: local-decoders-bound-connected-missing-particle-witnesses
requires: []
artifacts:
  - research/artifacts/conservative-syndrome-update-audit-2026-09-07.md
---

## Local control of attained finite configurations

The identity sigma tau=id implies injectivity of tau. Since tau(0)=0,
it also gives sigma(0)=0. If a finite configuration y lies in the image
of tau, its unique preimage is sigma(y). Locality and sigma(0)=0 imply

    supp(sigma(y)) subset supp(y) S^(-1).              (DG1)

Indeed, a coordinate g outside that set sees only zeros in gS. This
argument applies even when the original assertion of attainment allowed
an infinite preimage: the decoder forces that preimage to be finite.

## Separated attained components can be glued

Suppose y_1,...,y_r have finite supports Y_1,...,Y_r with no D-edge
between different supports, and suppose tau(x_i)=y_i. Replace each x_i
by its necessarily equal value sigma(y_i), so (DG1) holds.

No translated tau-memory gM can meet supp(x_i) and supp(x_j) for i!=j.
For otherwise there are u,v in S, m,n in M, p in Y_i and q in Y_j with

    p u^(-1)=gm,             q v^(-1)=gn.

It follows that

    p^(-1)q=u^(-1) m^(-1) n v in S^(-1) M^(-1) M S=D,

contradicting separation. Because 1_G belongs to M, this also implies
that the supports of the x_i are disjoint.

Let x be their binary union. At every output coordinate, the tau-memory
there sees nonzero data from at most one x_i. Its local rule therefore
agrees with tau(x_i) at that coordinate, or gives 0 when it sees none.
Thus tau(x) is exactly the union of the y_i. Applying this to the
D-connected components of y proves the gluing assertion.

## A supplied decoder bounds a missing witness

Write R=tau sigma. It fixes every point of the image of tau, and

    image(tau)={y : R(y)=y}.

The reverse inclusion follows from y=tau(sigma(y)). The memory of R
is contained in MS, in the specified order. If tau is not surjective,
choose y with R(y)!=y, then translate it so that the inequality occurs
at 1_G. Replace its coordinates outside MS by zero, obtaining z. Since
1_G belongs to MS, both R(z)(1_G)=R(y)(1_G) and z(1_G)=y(1_G).
Hence R(z)!=z, and z is a missing finite configuration with at most
|MS|=K particles.

Choose a missing finite configuration with the smallest particle number
n. It is nonzero because tau(0)=0, and n<=K by the preceding argument.
If its support had several D-connected components, each component
would have fewer particles, so minimality would make each component
attained. The gluing assertion would then make the entire configuration
attained, a contradiction. Its support is therefore D-connected.

Choose one occupied site p and translate p to 1_G. A connected graph
on n vertices has a simple path of at most n-1 edges from p to any
other vertex. Every edge multiplies the position on the right by an
element of D, so the translated support is contained in D^(n-1), and
therefore in D^(K-1). This proves the finite witness family and the
claimed sufficient condition. All statements concern finite subsets of
G and remain valid for nonabelian groups and groups with torsion.

## The conservative special case and the remaining correction task

The conservative-syndrome audit proves that an injective binary
particle-conserving rule attains the one- and two-particle sectors:
normalize the one-particle action by its equivariant right-coordinate
shift, and use the resulting finite permutation of interacting pair
orbits. Together with tau(0)=0, this excludes missing witnesses of
sizes 0,1,2 here. No conclusion about the remaining sizes follows
merely from the gluing argument.

In particular, under surjectivity of every lower-particle sector, any
missing n-particle configuration is connected at scale D and belongs
to finitely many translation orbits. This does not by itself force
surjectivity on the n-particle sector, whose entire orbit set can still
be infinite. The argument supplies no zero-index theorem for the action
on that larger orbit set. Its positive content is the explicit gluing
of separated attained components and the finite decoder-dependent bound
on the connected witnesses still needing correction.

## A nonlinear conservative marker involution

On Z, call an occurrence of adjacent ones, 11, a marker. For every
occurrence of one of the length-eight words

    11010011,               11001011,

swap its fourth and fifth bits (positions 3 and 4 when indexed from 0).
This exchanges the two displayed words, leaving all other coordinates
unchanged. The update is a cellular automaton: whether a bit changes
can be decided from the radius-four neighborhood around it.

The payload begins and ends with 0, and the two bits changed are either
10 or 01. The operation creates or destroys no occurrence of 11.
Within either displayed word, the only markers start at positions 0
and 6. Therefore distinct active words have disjoint payload intervals;
they may share marker bits, which are never changed. The full marker
set is invariant, and in the gap between the relevant markers the
operation simply exchanges 0100 and 0010. Eligibility of every such
gap is consequently invariant as well. Applying the rule twice restores
every payload and proves that the CA is an involution on the entire
full shift, including configurations with additional or overlapping
markers.

Each active payload retains exactly one 1, so the rule conserves total
particle number on finite configurations. It is nontrivial, sending
the finite support {0,1,3,6,7} to {0,1,4,6,7}. It fixes every
one-particle configuration. If this binary CA were linear over F_2,
locality and its values on all one-particle configurations would force
it to be the identity; therefore it is nonlinear.

Taking sigma=tau gives an explicit local decoder. For every finite
connected target y its lift is simply sigma(y), and the gluing theorem
then combines such lifts on separated components. This example verifies
a genuine finite interacting-cluster correction mechanism, while its
involutive nature makes it a reversible example rather than a proposed
Gottschalk counterexample.
