---
rg: 2
id: ring-simple-envelope-characteristic-proof
kind: route
title: Use the center of a simple ring for necessity and amplified endomorphisms for sufficiency
target: ring-simple-envelope-characteristic-obstruction
requires: []
artifacts:
  - research/artifacts/boone-higman-ring-route-repair-2026-09-08.md
---

If B is a nonzero simple unital ring and 0 != z in Z(B), the nonzero
ideal Bz equals B. Choose b with bz=1; centrality also gives zb=1.
The inverse of a central unit is central, so Z(B) is a field. Consequently
B has prime characteristic, or has characteristic zero and contains Q
centrally. In the latter case its additive group is torsion-free. A unital
injection R -> B preserves characteristic and transfers the applicable
necessary condition to R.

Conversely, in prime characteristic set F=F_p and A=R. In the
torsion-free case set F=Q and A=Q tensor_Z R. The map R -> A is
injective: rational localization kills precisely additive integer torsion.
In either case A is a nonzero unital algebra over the field F.

Choose an infinite cardinal kappa >= dim_F(A), and let W be the direct
sum of kappa copies of the vector space A. Represent A on W by
componentwise left multiplication. For each a != 0, the image contains
one independent nonzero vector a in every summand (apply the operator to
the vector 1 in that summand). Thus this operator has rank kappa.

In End_F(W), let J be the operators of rank less than kappa. This is
a two-sided ideal: compositions do not increase rank, and a finite sum of
cardinals less than an infinite cardinal kappa is still less than
kappa. This also covers singular kappa. Since dim(W)=kappa, J is
proper. The representation of A is injective modulo J by the rank
calculation above.

The quotient B=End_F(W)/J is simple. Given a nonzero class represented by
T, its rank is kappa. Choose a complement V to ker(T); both V
and T(V) have dimension kappa. Choose an isomorphism Q:W -> V and
extend the inverse of TQ:W -> T(V) to a linear map P:W -> W by choosing
a complement to T(V). Then PTQ=1. Hence every nonzero class generates
the unit ideal. This gives the required unital embedding R -> B.

Finally Z/6Z has composite characteristic and nonzero additive torsion.
It is finitely presented as a unital ring by the relation 6=0, and its
six-element operation tables decide equality. It violates the necessary
condition, regardless of any finiteness imposed on a proposed envelope.
