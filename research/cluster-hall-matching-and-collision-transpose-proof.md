---
rg: 2
id: cluster-hall-matching-and-collision-transpose-proof
kind: route
title: Match finitely many cluster types equivariantly and transpose their ordered-particle lift
target: finite-injective-conservative-binary-automata-are-surjective
requires:
  - finite-collision-operator-algebras-are-stably-finite
---

## The coefficient algebra and its faithful representation

For fixed n>=1 let C_n be the complex algebra of functions on G^n generated
by 1 and the relative-equality indicators

    p_(ij,s)(g_1,...,g_n)=1 if g_i^(-1)g_j=s, and 0 otherwise,

where i!=j and s is in G. Write D_n=C_n semidirect G^n, with the action

    (alpha_h f)(g)=f(gh)

using coordinatewise multiplication. Represent its group symbol u_h on
finitely supported functions by (u_h xi)(g)=xi(gh), and its coefficients
by pointwise multiplication. This representation is faithful: in

    (sum_h f_h u_h)xi(g)=sum_h f_h(g)xi(gh),

the finitely many points gh are distinct, so a unit input at one such
point isolates its coefficient. The algebra has an involution given by

    (f u_h)^*=alpha_(h^(-1))(conjugate(f)) u_(h^(-1)),

and the particular coefficients used below are rational and real. Thus
on our operators its representation is the ordinary transpose on the
basis of ordered tuples. The required
claim establishes stable finiteness of D_n for arbitrary G; we will use
its direct-finiteness consequence.

## Local decomposition into finitely many cluster types

Choose a finite memory M for tau, containing 1_G, so its output at g
reads x|_(gM). Put E=M^(-1)M. For a finite particle support X, join
p,q in X if p^(-1)q belongs to E. Distinct E-connected components cannot
meet the same translated memory gM.

Since tau fixes 0, its output on X is therefore the union of its outputs
on the components separately. These component outputs are disjoint:
an output 1 contributed by two different components would require gM
to meet both. Conservation says that each component C and its output
Y_C have equal cardinality.

Fix the total number n of input particles. Every component C has at most
n elements. After translating one of its elements to 1_G, all its sites
lie in E^(n-1), by taking simple paths in its connected graph. There are
therefore finitely many possible component types up to translation.

## Conservation gives a bounded matching, including stabilizers

Let C be one component and Y=Y_C its output support. For any Z subset Y,
truncate the input C to C_Z=C intersect ZM. At every site of Z the local
input is unchanged, so the output of C_Z contains Z. Conservation yields

    |Z| <= |C_Z| = |C intersect ZM|.                  (CH1)

Hall's finite marriage theorem now gives a perfect matching between
output sites q in Y and input sites p in C, with p in qM. Thus matched
positions satisfy q=p d for some d in M^(-1).

Let H be the translation stabilizer of C. It is finite, since h->hp for
any p in C injects H into C. Equivariance gives H subset Stab(Y), and
injectivity on finite configurations gives the reverse inclusion:
tau(hC)=hY=Y=tau(C) implies hC=C. Hence Stab(Y)=H.

The matching graph in (CH1) is H-invariant, and H acts freely on its
input and output vertices, because these vertices are elements of G.
Every H-orbit has |H| vertices. Apply (CH1) to unions of output orbits
and divide by |H| to obtain Hall's condition for the finite quotient
graph on input and output H-orbits. Choose a perfect matching of those
orbits. For each matched pair of orbits choose one adjacent pair p,q,
then match hp with hq for every h in H. This is well-defined by freeness
and gives an H-equivariant perfect matching with the same displacement
bound.

For each of the finitely many translation types of components of size
at most n, choose one such matching. Transport it by G to all translates.
The result is independent of the translating element because the chosen
matching is stabilizer-equivariant. Write mu_C:C->Y_C for the resulting
G-equivariant family of bijections.

## The ordered lift uses only finitely many relative tests

Given an ordered tuple g=(g_1,...,g_n) of distinct sites, form its support
X and its E-components. Send each coordinate g_i to mu_(C_i)(g_i),
where C_i is its component. Component outputs are disjoint, so the
result is again a distinct ordered tuple, with support tau(X).

This map commutes with diagonal left translation and with permutation
of the tuple coordinates. It is injective: equality of output tuples
gives equality of their supports; finite-configuration injectivity of tau
then gives the same input support. The fixed matching on that support
is a bijection, and hence also recovers the input ordering.

Every output coordinate has the form g_i d_i with d_i in M^(-1).
Moreover, its chosen displacement depends on only finitely many
relative-equality predicates. Indeed, the E-component of g_i is found
from the finite graph whose edges are the tests

    g_j^(-1)g_k=s,                 s in E.

For j in that component the relative coordinate g_i^(-1)g_j lies in
E^(n-1). Tests against this finite set identify the entire rooted
component shape g_i^(-1)C_i. Its matching at 1_G fixes the displacement
d_i. Thus each simultaneous displacement class is a finite Boolean
combination of relative-equality indicators and belongs to C_n.

Extend the map by identity on tuples with repeated coordinates. This
set is itself defined by finitely many relative-equality tests with
s=1_G. The distinct and repeated parts are preserved separately, so
the extension remains injective.

Let q_d in C_n be the indicator that this extension uses displacement
d=(d_1,...,d_n). Only finitely many d occur, with the identity displacement
also allowed. On tuple basis vectors its linearization is

    T=sum_d u_(d^(-1)) q_d,       T delta_g=delta_(g d(g)).

Thus T belongs to D_n. The coefficient functions q_d partition G^n.
The proof has supplied a finite expression in the algebra, rather than
an arbitrary orbitwise operator with uncontrolled coefficients.

## An explicit transpose inverse forces surjectivity

The algebraic transpose T^* belongs to D_n by its involution. Since T
sends different tuple basis vectors to different tuple basis vectors,
direct basis computation gives

    T^* T=I.

This is also an identity in D_n by faithfulness. In particular, the left
inverse is explicitly supplied; it is not deduced from injectivity of
an arbitrary infinite-dimensional operator. Direct finiteness of D_n
gives T T^*=I.

If an ordered tuple were missing from the image of T, its basis vector
would be killed by T^* and hence by T T^*, contradicting this identity.
Therefore T is surjective. Repeated tuples map only to themselves, so
each distinct ordered output has a distinct ordered preimage. Passing
to supports proves surjectivity of tau on the n-particle sector.

The zero-particle sector is the singleton {0} and is fixed. If G is
finite and n>|G|, the n-particle sector is empty and the assertion is
vacuous; the identity extension on repeated tuples is still valid.
These observations cover all boundary cases.

We have proved that every finite configuration is attained. Finite
configurations are dense in {0,1}^G, and the image of tau is compact,
hence closed. Consequently its image is the entire full shift. Global
injectivity of tau was not used beyond the weaker stated injectivity
on finite configurations.
