---
rg: 2
id: kt-wreath-hyperlinear-iff-double-proof
kind: route
title: Instantiate the general coset-wreath equivalence at the Kun--Thom pair
target: kt-wreath-hyperlinear-iff-double-hyperlinear
requires:
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
  - kt-q2-double-hyperlinear-iff-relative-embeddable
---

Apply `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` to the
countable inclusion `Gamma <= G` of the Kun--Thom Theorem E pair.  Its object
(1), the ordinary binary coset wreath `(direct_sum_(A/C) C_2) rtimes A`, is at
`(A,C) = (G,Gamma)` exactly the Kun--Thom binary wreath `W`; its object (4) is
the double `D = G *_Gamma G`; and its condition (6) is `RE/C` of
`L(Gamma) <= L(G)`.  The theorem gives (1) <=> (4) <=> (6), which is the
present statement (1) <=> (2) <=> (3).

The second prerequisite,
`kt-q2-double-hyperlinear-iff-relative-embeddable`, is the same pair's
double-to-`RE/C` equivalence, established independently through the tensor-swap
theorem; requiring it makes the double column of the equivalence explicit for
this pair rather than only implied by the general node.  Both prerequisites are
established, so the target is established.
