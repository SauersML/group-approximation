---
rg: 2
id: four-pauli-cross-gram-exact-completeness-firewall-proof
kind: route
title: Telescope the alternating polynomial through the proposed common contraction
target: four-pauli-cross-gram-exact-completeness-firewall
requires:
  - four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap
---

Amitsur--Levitzki gives

```text
s4(C_1,C_2,C_3,C_4)=0,                                (PCP1)
```

because all four `C_j` lie in one copy of `M_2`.  For each of the twenty-four
degree-four monomials, telescope one factor at a time through `T`.  All
remaining factors are contractions, and each residual
`D_jT-TC_j` occurs twenty-four times in the resulting sum.  Hence

```text
||s4(D)T-Ts4(C)||_2
 <= 24 sum_(j=1)^4 ||D_jT-TC_j||_2.                   (PCP2)
```

By `(PCF1)`, contractivity of right multiplication by `T`, and unitarity of
`W`,

```text
||s4(D)T||_2
 >= ||8WT||_2-||(s4(D)-8W)T||_2
 >= 8||T||_2-epsilon.                                 (PCP3)
```

Combine `(PCP1)--(PCP3)` to obtain `(PCF2)`.  For the transverse Pauli
tuple, the exact commutator expansion gives

```text
s4(D)=8D_1D_2D_3D_4,
```

and the product on the right is unitary.  If `||T||_2^2>=5/64`, `(PCF2)`
becomes `(PCF3)`.  Finally Cauchy--Schwarz gives

```text
sum_j ||D_jT-TC_j||_2^2
 >= (1/4)(sum_j ||D_jT-TC_j||_2)^2
 >= 5/2304,
```

which is `(PCF4)`.
