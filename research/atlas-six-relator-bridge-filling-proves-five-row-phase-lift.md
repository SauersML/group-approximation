---
rg: 2
id: atlas-six-relator-bridge-filling-proves-five-row-phase-lift
kind: route
title: Fill four rank-three bridges and telescope the five phase circulations
target: atlas-five-row-operator-phase-lift
requires:
  - atlas-six-relator-quotient-identifies-h-bridge
---

Let `R_6` denote the six relators in `(SXB1)`.  Once `(SXB2)` is known, fix
for every standard generator `t in T` a van Kampen expression

```text
i_2(t)i_1(t)^-1=product_(nu=1)^(N_t) a_(t,nu)
                    r_(t,nu)^(epsilon_(t,nu)) a_(t,nu)^-1,
                    r_(t,nu) in R_6.                         (SXF1)
```

For a relative chart unitary `U`, write

```text
d_t(U)=||rho(t)U rho(t)^*-U||_2.
```

Evaluation of `(SXF1)`, conjugation invariance, and telescoping give

```text
d_t(U)<=sum_(nu=1)^(N_t) e_(r_(t,nu))(U).              (SXF2)
```

Every edge difference `v_jr^-1 u_jr` lies in the fixed finite group `H`.
Choose a word in `T union T^-1` for each of these nineteen differences and
let `D` be the maximum chosen length.  Since `d_(t^-1)=d_t`, a second
telescope gives

```text
||Phi_u(U)-Phi_v(U)||_2
 = d_(v^-1 u)(U)
 <= D (sum_(t in T)d_t(U)^2)^(1/2).                  (SXF3)
```

Let `n_(t,r)` be the number of occurrences of the relator `r in R_6` in
the chosen filling for bridge generator `t`, and let `N=(n_(t,r))` be the
resulting `4 by 6` nonnegative matrix.  Equation `(SXF2)` says, entrywise,

```text
(d_t)_(t in T) <= N (e_r)_(r in R_6),
```

and hence

```text
sum_t d_t(U)^2 <= ||N||_op^2 sum_(r in R_6)e_r(U)^2. (SXF3a)
```

If row `j` has `m_j` phase edges, Cauchy--Schwarz gives

```text
l_j(U)^2 <= m_j sum_(r=1)^(m_j)
                    ||Phi_(u_jr)(U)-Phi_(v_jr)(U)||_2^2.
```

Here `m_j` is respectively `3,4,4,4,4`.  Applying `(SXF3)` to each edge and
then `(SXF3a)` yields the completely explicit bound

```text
sum_j l_j(U)^2
 <= (sum_j m_j^2) D^2 ||N||_op^2 sum_(r in R_6)e_r(U)^2
 = 73 D^2 ||N||_op^2 sum_(r in R_6)e_r(U)^2.          (SXF3b)
```

Thus one may take `C_5=73 D^2 ||N||_op^2` in

```text
sum_j l_j(U)^2
 <= C_5 (sum_j e_j(U)^2+e_int(U)^2).                  (SXF4)
```

The construction is unchanged after tensoring the regular chart by an
arbitrary multiplicity space.  Thus `C_5` is multiplicity independent and
`(SXF4)` is exactly `(FPL4)`.
