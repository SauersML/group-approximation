---
rg: 2
id: corner-localized-non-ce-bcs-energy-gap
kind: claim
title: Non-CE BCS soundness survives on every approximately reducing matrix corner
distinct_from:
  non-ce-bcs-has-finite-dimensional-forbidden-mass-gap: that assumes exact contextwise commutation on the whole matrix algebra; this allows all BCS relations and the reducing-corner condition to be approximate simultaneously.
  scaled-kazhdan-transport: that produces approximately reducing carriers from group relations; this consumes any such carrier and proves that BCS failure cannot dilute inside it.
---

Fix a finite BCS `B` having tracial states but no Connes-embeddable tracial
state, and fix an order on every context.  Let `R_B` be the finite list
consisting of

- the involution polynomials `Z_x^2-I`;
- the context commutators `[Z_x,Z_y]`; and
- the ordered forbidden products
  `product_(x in U_c) (I+(-1)^(a_x) Z_x)/2`.

There is a constant `beta_B^corner>0` such that, for every `d`, every unitary
tuple `(Z_x) subset U(d)`, and every orthogonal projection `Q in M_d(C)`,

```text
sum_x ||[Q,Z_x]||_(2,d)^2
+ sum_(R in R_B) ||R(Z)Q||_(2,d)^2
   >= beta_B^corner tau_d(Q).                         (CLG1)
```

Thus the non-CE soundness gap is hereditary under conditioning, without a
lower bound on `tau_d(Q)`.  In particular, a compressor-prefix carrier is
allowed to shrink with the matrix dimension: if its normalized commutator
and localized BCS energies are `o(tau_d(Q))`, then it would itself produce a
Connes-embeddable BCS trace, which is impossible.

The use of the original shared words is essential.  Independently exactifying
each context before cutting to `Q` would lose the common-variable information
and would not imply `(CLG1)`.
