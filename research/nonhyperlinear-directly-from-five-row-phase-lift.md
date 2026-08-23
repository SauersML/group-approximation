---
rg: 2
id: nonhyperlinear-directly-from-five-row-phase-lift
kind: route
title: The five-row phase inequality directly obstructs the canonical Leavitt trace
target: non-hyperlinear-group
requires:
  - atlas-five-row-operator-phase-lift
  - leavitt-regular-atlas-separating-refinement
  - atlas-charts-overlap-trivially
  - regular-atlas-linearized-h-coercivity
---

Put

```text
Q=L_(F_2)(1,2)^x.
```

The five-row phase lift already proves that `Q` is non-hyperlinear; the
two-`S3` source packet and its separate lower wall are not needed for this
implication.

Indeed, the two marked `A8` charts in `Q` intersect trivially.  Hence, for
some standard transvection `t` of

```text
H=diag(GL_3(2),1),
```

the bridge word

```text
b_t=i_2(t)i_1(t)^-1
```

is nontrivial in `Q`.

Assume for contradiction that `Q` is hyperlinear.  Apply
`leavitt-regular-atlas-separating-refinement` to the one-element separation
window `{b_t}`.  This gives canonical regular-`A8` relative-chart models

```text
U_n in U(20160 k_n)
```

such that

```text
max_(s in bar_S) ||pi_(U_n)(s)-1||_2 -> 0,
||pi_(U_n)(b_t)-1||_2 -> sqrt(2).                     (DFP1)
```

For the canonical relative-chart coordinates, the second quantity is
exactly the `t`-covariance defect:

```text
||pi_(U_n)(b_t)-1||_2
 = ||rho(t)U_n rho(t)^*-U_n||_2.                      (DFP2)
```

Apply `regular-atlas-linearized-h-coercivity` to `X=U_n`.  With the five
indices `J={0,11,30,44,55}`, it gives

```text
sum_(ell=1)^4 ||rho(t_ell)U_n rho(t_ell)^*-U_n||_2^2
 <= C_lin sum_(j in J) l_j(U_n)^2.                   (DFP3)
```

Equations `(DFP1)--(DFP3)` imply

```text
liminf_n sum_(j in J) l_j(U_n)^2 >= 2/C_lin > 0.     (DFP4)
```

On the other hand, each of the five boundary words `s_j` and the interior
word `c_19243` is a fixed consequence of the canonical packet `bar_S`.
Choose fixed van Kampen expressions.  Telescoping `(DFP1)` through those
expressions gives

```text
sum_(j in J) e_j(U_n)^2+e_int(U_n)^2 -> 0.           (DFP5)
```

Now apply `atlas-five-row-operator-phase-lift` to `U_n`.  Its
multiplicity-independent constant `C_5` and `(DFP5)` force the left side of
`(DFP4)` to tend to zero, a contradiction.  Therefore `Q` is
non-hyperlinear.

This also supplies a sharp audit of the remaining five-row claim.  If `Q`
is hyperlinear, the sequence above makes

```text
[sum_j e_j(U_n)^2+e_int(U_n)^2]
---------------------------------  -> 0
          sum_j l_j(U_n)^2
```

with a denominator bounded away from zero.  Thus hyperlinearity of the
explicit Leavitt group *refutes* the proposed inequality.  Conversely the
inequality proves that same group non-hyperlinear.  The five-row lift is
therefore not a routine local packet estimate waiting to be fed into a
larger obstruction: it is itself a direct, goal-level finite-matrix
separation theorem.

The exact finite falsification gate remains
`atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test`: one finite
quotient retaining a standard `H` bridge refutes the inequality at zero
defect.  In the absence of such a quotient, excluding exact finite zeros
still does not supply the required uniform amplified gap.
