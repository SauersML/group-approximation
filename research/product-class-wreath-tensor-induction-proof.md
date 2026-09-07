---
rg: 2
id: product-class-wreath-tensor-induction-proof
kind: route
title: Run the marked-site tensor induction inside the chosen group class
target: wreath-finiteness-transfers-from-product-closed-classes
requires:
  - split-local-corner-extensions-preserve-stable-finiteness
---

The algebraic construction is the one written in full in
`finite-particle-wreath-separation-proof`. Its representation and
separation steps hold for arbitrary A and G; residual finiteness occurs
only in its induction on coefficient group algebras. We give that
construction and the replacement induction explicitly here.

Put D=direct_sum_(x in X) k[A], let C_0=k plus D be the external
unitization, and put R=C_0 semidirect G. Evaluation at the scalar
coordinate gives a split exact sequence

    0 -> J -> R -> k[G] -> 0.

For each orbit O with representative o, the corresponding ideal is
Mat_fin(O,k[A x G_o]). To verify this, choose t_x o=x; the arrow term
e_x a u_g corresponds to E_(x,y)(a[t_x^(-1)g t_y]), where y=g^(-1)x.
Multiplication matches matrix multiplication, and g=t_x h t_y^(-1)
produces every coefficient a[h]. Thus J is the direct sum of these ideals.

We prove, simultaneously for every H in C, that

    S(H,r)=k[H] tensor_k R^(tensor r)

is stably finite for all integers r>=0. At r=0 this is the class
hypothesis. Tensoring the split exact sequence with S(H,r-1) gives
quotient S(H x G,r-1) and ideal

    direct_sum_O Mat_fin(O,S(H x A x G_o,r-1)).

All groups H x G and H x A x G_o belong to C, by subgroup and finite-
product closure. The induction hypothesis makes the quotient and all
finite diagonal ideal corners stably finite. The split local-corner
extension lemma therefore proves the induction step. In particular all
R^(tensor r) are stably finite, by taking H trivial.

For n in N=direct_sum_X A let v_n in C_0 be the function with values
[n(x)] at x and scalar value 1 at the extra infinity coordinate. It is
an invertible element of C_0. The maps

    n g -> v_n u_g -> (v_n u_g)^(tensor r)

are group homomorphisms, and extend linearly to algebra homomorphisms
Phi_r:k[N semidirect G]->R^(tensor r). Identify the target with
C_0^(tensor r) semidirect G^r. Distinct g have distinct formal tags
(g,...,g).

For a nonzero z=sum_g b_g[g], choose a finite set F containing all lamp
sites occurring in the b_g. If F is nonempty, evaluate the |F| coefficient
factors at the distinct sites of F. On each b_g in k[A^F], this is exactly
the natural identification with k[A^(|F|)], so a nonzero b_g remains
nonzero in its formal tag. If F is empty, use one coefficient factor and
its scalar evaluation. Therefore intersection_r ker Phi_r=0.

The separating family has stably finite targets. A matrix inverse defect
must vanish in every target and hence vanish in k[A wr_X G]. This proves
the transfer theorem with precisely the stated class assumptions.
