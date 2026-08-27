---
rg: 2
id: marked-star-outer-corrected-whitehead-proof
kind: route
title: Correct the middle-prefix swaps by the matching outer-coordinate Weyls
target: marked-star-outer-corrected-whiteheads-are-quarter-swaps
requires:
  - marked-root-star-carries-three-anchored-cells
  - same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps
---

Write `alpha_m=m+3` and `k_m=m+6`.  The same coefficient calculation as in
the common-center Whitehead row gives

```text
J_m x_(alpha_m,k_m)(a_m) J_m^(-1)
  =x_(alpha_m,k_(m+1))(a_(m+1)),
J_m x_(k_m,2)(b_m) J_m^(-1)
  =x_(k_(m+1),2)(b_(m+1)),                            (1)
```

and the reverse formulas for the `(m+1)` arms.  The first root in `(1)`
still has outer index `alpha_m`; this is the forked arm in `(MSW8)`.

The constant Weyl `L_m=w_(alpha_m,alpha_(m+1))(1)` swaps the two outer
indices, fixes the middle indices and terminal index `2`, and therefore
turns `(1)` into

```text
Ad(L_mJ_m):(A_m,B_m)<->(A_(m+1),B_(m+1)).             (2)
```

All root indices of the `L_m` lie in `{4,5,6}`, while all root indices of
the `J_m` lie in `{7,8,9}`.  Hence the two families commute elementwise.
The `L_m` satisfy the adjacent-transposition relations in the embedded
constant `St_3(F_2)=SL_3(F_2)` subgroup, and the `J_m` satisfy the same
relations by the literal prefix-Whitehead braid.  Therefore their products
`U_m=L_mJ_m` are involutions and satisfy `(MSW5)`.

The outer Weyls swap the central roots `x_42(q),x_52(q),x_62(q)`, while the
prefix Whiteheads fix all three.  Both families fix `z=x_13(q)`.  Hence
each `U_m` preserves the all-negative star projection `E`.

On `EH`, equation `(2)` implements the corresponding automorphism of the
three-qubit Pauli algebra.  Two implementers differ by a unitary in its
commutant, which proves `(MSW6)`.  Cancelling the identical label braid
from `(MSW5)` gives the reservoir braid, and

```text
(V_1V_2)V_1(V_1V_2)^(-1)=V_2,
```

so the two reservoir involutions are conjugate.

Finally `A_1=x_47(a_1)` and `A_2=x_58(a_2)` commute with `z` and with each
of `x_42(q),x_52(q),x_62(q)`: every relevant pair has the same initial
index or a noncomposable root rectangle.  Thus both `A_1` and `A_2A_1`
reduce `E`, proving `(MSW7)`.  Since an adjacent swap on two qubits has a
two-dimensional negative eigenspace after tensoring by the third qubit,
both label fractions in `(MSW6)` are `2/8=1/4`.

In the standard eight-dimensional label representation, each Pauli
generator has negative multiplicity four and each adjacent swap has
negative multiplicity two.  All generators therefore have determinant one,
as does every word in the packet.  An involutory word consequently has an
even-dimensional negative eigenspace.  This proves the packet-wide
one-eighth determinant fence stated in the claim.
