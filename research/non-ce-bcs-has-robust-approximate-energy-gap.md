---
rg: 2
id: non-ce-bcs-has-robust-approximate-energy-gap
kind: claim
title: A non-CE BCS has a dimension-free group-word energy gap
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  non-ce-bcs-has-finite-dimensional-forbidden-mass-gap: that assumes exact commutation inside every context and measures traces of genuine forbidden projections; this allows approximate context commutation and measures positive squared norms of ordered forbidden products.
  finite-schur-clifford-packet-flexible-hs-exactification: that rounds each fixed finite context packet in flexible dimension; this theorem applies directly to the original shared unitary word and needs no simultaneous choice of the local corrections.
  multiplicity-surplus-is-blind-to-the-non-ce-input: that warns a beta-only return mechanism can also fire on classical unsatisfiability; this theorem consumes non-embeddability directly through the full contextual approximate tuple.
---

Let `B` be the fixed finite BCS with a tracial state but no Connes-embeddable
tracial state.  Fix an order on each context.  There is `beta_B^rob>0` such
that every finite-dimensional tuple of unitaries `(Z_x)` obeys

```text
sum_x ||Z_x^2-I||_2^2
+ sum_c sum_({x,y} subset U_c) ||[Z_x,Z_y]||_2^2
+ sum_c sum_(a in F_c)
    || product_(x in U_c, fixed order)
         (I+(-1)^(a_x) Z_x)/2 ||_2^2
  >= beta_B^rob.                                           (RFMG)
```

The same matrix `Z_x` occurs in every context containing the BCS variable
`x`; no simultaneous correction of independently exactified context copies is
assumed.  If the involution and commutator parts are small, local flexible
exactification of a fixed Schur--Clifford packet changes each ordered forbidden
product by only a fixed multiple of the packet defect.  Hence `(RFMG)` supplies
positive total rank-jump mass unless the ordinary group relators already pay a
constant HS energy.
