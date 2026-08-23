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

Every endpoint `u_jr,v_jr` of the nineteen boundary phase edges lies in the
fixed finite group `H`.  Choose a word of length at most `D` in `T` for every
such endpoint.  A second telescope gives

```text
||Phi_u(U)-Phi_v(U)||_2
 <= d_u(U)+d_v(U)
 <= D sum_(t in T) d_t(U).                            (SXF3)
```

(Replacing `D` by twice the maximum chosen length merely changes the fixed
constant.)  Sum `(SXF3)` inside each of the five signed rows and use
Cauchy--Schwarz first over its at most four edges and then over the finitely
many occurrences in `(SXF1)`.  There is therefore one explicit finite
constant `C_5`, depending only on the four fixed fillings, such that

```text
sum_j l_j(U)^2
 <= C_5 (sum_j e_j(U)^2+e_int(U)^2).                  (SXF4)
```

The construction is unchanged after tensoring the regular chart by an
arbitrary multiplicity space.  Thus `C_5` is multiplicity independent and
`(SXF4)` is exactly `(FPL4)`.

