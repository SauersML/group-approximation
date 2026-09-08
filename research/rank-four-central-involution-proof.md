---
rg: 2
id: rank-four-central-involution-proof
kind: route
title: Square two elementary signed swaps to obtain minus the identity
target: rank-four-elementary-center-obstructs-simplicity
requires: []
---

Write e_ij(a)=I+aE_ij. The elementary word

    w_ij = e_ij(1) e_ji(-1) e_ij(1)

has the block [[0,1],[-1,0]] in coordinates i,j, and fixes the other
coordinates. Squaring gives -I on that two-coordinate block. Therefore

    w_12^2 w_34^2 = -I_4 in EL_4(L).

This scalar matrix is central and has order two, because 2*1_L != 0.
The subgroup it generates is proper: e_12(1) has a nonzero off-diagonal
entry and is neither I_4 nor -I_4. Thus a nontrivial proper normal
subgroup exists, as claimed. This computation uses no commutativity of L.
