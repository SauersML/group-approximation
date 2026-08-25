---
rg: 2
id: atlas-five-row-energy-equals-h-bridge-energy
kind: claim
title: The five Atlas linear rows and the four H bridges have uniformly equivalent energy
distinct_from:
  regular-atlas-linearized-h-coercivity: that proves the four infinitesimal covariance rows are bounded by the five derivative rows; this proves the reverse bound and identifies the covariance rows with literal bridge-word defects in every common frame.
  atlas-five-row-operator-phase-lift: that asks nonlinear six-relator energy to control the five linear rows; this replaces the five large integral rows by four short group-word bridges without changing the uniform problem.
  atlas-six-relator-hyperlinear-escape-test: that gives the qualitative exact-ultraproduct criterion using survival of at least one bridge; this gives the quantitative two-sided equivalence of total bridge energy and five-row energy at every matrix multiplicity.
---

Let

```text
A(U)=sum_(j in {0,11,30,44,55}) ||rho(z_j)U||_2^2
```

on a regular `A8` chart of arbitrary external multiplicity.  For the four
standard transvections `t_1,...,t_4` generating
`H=diag(GL_3(2),1)`, put

```text
D_H(U)=sum_(ell=1)^4 ||rho(t_ell)U-U rho(t_ell)||_2^2. (FBE1)
```

There are constants `0<c_H<=C_H<infinity`, depending only on the fixed
regular packet and not on the external multiplicity, such that

```text
c_H D_H(U)<=A(U)<=C_H D_H(U).                         (FBE2)
```

In common-frame coordinates for the two marked `A8` charts, if

```text
b_ell=i_2(t_ell)i_1(t_ell)^(-1),
```

then exactly

```text
||pi_U(b_ell)-1||_2
 =||rho(t_ell)U-U rho(t_ell)||_2.                     (FBE3)
```

Consequently `atlas-five-row-operator-phase-lift` is equivalent, up to a
fixed change of constant, to the shorter relative-presentation inequality

```text
sum_ell ||pi_U(b_ell)-1||_2^2
 <=C_B [sum_(j in J)||pi_U(s_j)-1||_2^2
                  +||pi_U(c_19243)-1||_2^2].          (FBE4)
```

This equivalence retains the common-orbit identities automatically: all
terms are evaluated in the same relative chart unitary `U`.  It does not
free private phase variables.

DERIVATION
atlas-five-row-h-bridge-equivalence-proof
