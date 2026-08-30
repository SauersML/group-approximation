---
rg: 2
id: whitehead-injective-via-waldhausen-higman-rope
kind: route
title: Use a Whitehead-acyclic free double as the edge in Higman's rope
target: whitehead-injective-torsion-order-preserving-higman-embedding
requires: [torsion-free-higman-embedding, amalgam-torsion-permanence-needs-no-cyclic-reduction, hnn-torsion-orders-equal-base-torsion-orders, waldhausen-free-double-whitehead-space-contractible, waldhausen-hnn-vertex-whitehead-injectivity]
---

Let K=<X | S>, where X is finite and S is recursively enumerable. Write
F=F(X) and R=ker(F->K), so R is recursively enumerable as a set of words.
Take two copies of F and form

    L = F_1 *_R F_2.

The presentation with generators X_1 union X_2 and recursively enumerated
relations r_1=r_2 for r in R shows that L is finitely generated and
recursively presented. It is torsion-free because it is an amalgam of two
torsion-free free groups. There is a natural epimorphism

    pi : L -> K

induced by the quotient map on both free factors.

Apply the torsion-free Higman embedding theorem to L. It gives an embedding

    iota : L -> P

with P finitely presented and torsion-free. Put V=P x K and define two
injective maps

    alpha(l) = (iota(l), 1),
    beta(l)  = (iota(l), pi(l)).

Both are injective because their first coordinate is iota. Form the HNN
extension

    H = < V, t | t alpha(l) t^-1 = beta(l), l in L >.

Fournier-Facio--Zaremsky, Finiteness properties and Higman's rope trick,
arXiv:2607.21727, Definition 1.5 and Lemma 1.6, prove that this H is finitely
presented. Normal form embeds V and hence embeds K via k |-> (1,k).

Now apply the two Waldhausen calculations. Since L is the free-group double
F*_R F, [[waldhausen-free-double-whitehead-space-contractible]] gives
contractible Wh_Z(L). Consequently
[[waldhausen-hnn-vertex-whitehead-injectivity]] makes Wh(V)->Wh(H)
injective. The inclusion K->V is split by the projection P x K -> K, so
functoriality makes Wh(K)->Wh(V) split-injective. Their composite
Wh(K)->Wh(H) is injective.

Finally P is torsion-free, hence Tord(P x K)=Tord(K). By
[[hnn-torsion-orders-equal-base-torsion-orders]], the outer HNN extension
has

    Tord(H)=Tord(P x K)=Tord(K).

This proves all three assertions: finite presentability of H, injectivity on
Whitehead groups, and exact preservation of torsion orders. QED
