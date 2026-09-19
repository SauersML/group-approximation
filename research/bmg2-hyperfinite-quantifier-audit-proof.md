---
rg: 2
id: bmg2-hyperfinite-quantifier-audit-proof
kind: route
title: Keep the hyperfinite accuracy and bounded-complexity gap quantifiers in their valid order
target: bmg2-does-not-exclude-hyperfinite-atlas
requires:
  - leavitt-atlas-full-coefficient-purification
  - leavitt-regular-atlas-block-monomial-gap
---

Fix `eta>0` and grant the strongest lifting and polar-rounding conclusion
used by the proposed route.  Its rounded unitary `V_i^(eta)` is
`C_0 eta`-close to `U_i`, so the fixed-word Lipschitz estimate gives

```text
limsup_omega F(V_i^(eta)) <= C eta.
```

If `R(eta)` is the largest simple summand size in the approximating algebra,
then its whole coefficient weight is counted by `w_(R(eta))`.  Applying
`(BMG2)` and taking the ultralimit yields exactly

```text
e_(R(eta)) <= C^2 eta^2.
```

The integer `R(eta)` was chosen only after `eta`; it cannot be held fixed
while `eta` tends to zero.  Conversely, holding `R` fixed supplies no reason
that the coefficient tuple approaches an algebra of that fixed size.

Finally, positive purification itself gives dimensions `r_i->infinity` with
fixed-dimensional energies `E_(r_i)->0`.  Since
`e_(r_i)=min_(r<=r_i)E_r`, one has `e_(r_i)->0` along that subsequence.
Thus the rate inequality obtained above is compatible with every premise of
the proposed argument.  The exchanged-quantifier conclusion `(QF4)` needs
an additional approximation modulus and does not follow from hyperfiniteness.
