---
rg: 2
id: finite-product-table-transfer-proves-lef-ring-finiteness
kind: route
title: Transfer the complete finite support table of an inverse defect to a finite group
target: lef-group-rings-over-stably-finite-rings-are-stably-finite
requires:
  - rf-lamps-preserve-stable-finiteness-for-arbitrary-actions
---

Suppose VU=I_n but UV!=I_n in M_n(R[A]). Let S contain 1 and every
group label in every entry of U and V. Put E=S union SS. The LEF
property gives an injective map theta:E->L to a finite group preserving
all products internal to E. In particular theta(1)^2=theta(1), so
theta(1)=1.

Replace each label a in U,V by theta(a), retaining its R-coefficient,
and call the resulting matrices U',V' over R[L]. For every a,b in S,

    theta(a) theta(b)=theta(ab).

Every product label in either matrix multiplication belongs to SS.
Injectivity on E preserves both collisions and noncollisions among
these labels. Consequently each coefficient sum in V'U' and U'V'
is exactly the original coefficient sum with its group label renamed.
This preserves the order of all R-coefficient products, so commutativity
of R is unnecessary. We obtain V'U'=I_n and U'V'!=I_n.

The group ring R[L] is a free right R-module on the finite basis L.
Left multiplication is right R-linear and faithful, giving a unital
embedding

    R[L] -> End_R(R[L]_R) ~= M_(|L|)(R).

Applying this embedding entrywise contradicts stable finiteness of R.
The argument works for every n, proving the coefficient-ring theorem.

For completeness, a finite subset of A^j projects into finite subsets
of A in each coordinate. Enlarge the coordinate subsets to include
the required products and choose their finite LEF realizations. The
product of these maps is injective on the original subset and preserves
its products. Thus A^j is LEF for every finite j.

If k[G] is stably finite, so is each unital subalgebra k[H], H<=G.
The result just proved applies to

    (k[H])[A^j] ~= k[A^j x H].

The general coefficient hypothesis in
`rf-lamps-preserve-stable-finiteness-for-arbitrary-actions`, proved in
`diagonal-tensor-orbit-corner-induction-proof`, now gives stable
finiteness of k[A wr_X G]. That induction after its base step does
not require residual finiteness. The converse follows from the unital
copy of k[G] inside the wreath group algebra.
