---
rg: 2
id: a4-near-context-centralizer-product-rounding
kind: claim
title: Vanishing A4 pair-cube defect forces the relative unitary into the product of the two cyclic centralizers
---

Let

```text
rho_n = m_n Reg(A4),
A_n = rho_n(a),
B_n = rho_n(b),
```

where `a^3=b^2=(ba)^3=1`, and let `U_n` be arbitrary unitaries on the
same spaces.  Put

```text
C_A,n = U(rho_n(<a>)'),
C_B,n = U(rho_n(<b>)').
```

If

```text
||(U_n B_n U_n^* A_n)^3-1||_2 -> 0,
```

then

```text
dist_2(U_n, C_A,n C_B,n) -> 0.                       (A4-CENT-ROUND)
```

Thus, on an exact regular A4 margin, one vanishing mixed pair-cube defect is
asymptotically equivalent to a product-of-centralizers constraint on the
relative chart frame.  The statement is uniform under arbitrary external
amplification; no fixed multiplicity bound is assumed.

For the atlas this converts every shortest A4 pair-cube separately into a
geometric constraint on the single relative `A8` chart unitary.  The global
problem is therefore an intersection/agreement problem among finitely many
such centralizer products, not a local finite-group stability problem.
