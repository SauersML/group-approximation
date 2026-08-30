---
rg: 2
id: waldhausen-hnn-vertex-whitehead-injectivity-proof
kind: route
title: Read the constant Nil arrow in Waldhausen's general HNN fibration
target: waldhausen-hnn-vertex-whitehead-injectivity
requires: []
---

Use Remark 3 following Corollary 17.2.3 of Waldhausen, Algebraic K-theory of
generalized free products, Part 2, Annals of Mathematics 108 (1978),
205--256, DOI 10.2307/1971166. The remark explicitly treats the general
case, so Corollary 17.2.3's regular-coherence hypothesis is not being
silently imposed.

For the HNN extension it gives a homotopy fibration segment

    Omega BQ(Nil) x Wh_Z(L)
        --(pt, Wh(alpha_*) - Wh(beta_*))--> Wh_Z(V)
        --> Wh_Z(H)^*.

The printed pt means that the Nil factor maps constantly to the vertex
Whitehead space. If Wh_Z(L) is contractible, the first arrow is therefore
zero on pi_1. Exactness of the homotopy sequence makes

    pi_1 Wh_Z(V) -> pi_1 Wh_Z(H)^*

injective.

The remark after Corollary 17.1.3 identifies the starred Whitehead space as a
union of path components of the ordinary Whitehead space. Its inclusion has
the same fundamental group at the zero basepoint. Proposition 15.7 identifies
these fundamental groups with Wh(V) and Wh(H). Hence Wh(V)->Wh(H) is
injective. QED

This argument neither discards the Nil term nor claims L is regular
coherent: the Nil term is present but its displayed map is constant, and
only the separate hypothesis Wh_Z(L) contractible is used.
