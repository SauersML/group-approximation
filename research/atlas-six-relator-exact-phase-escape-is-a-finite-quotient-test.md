---
rg: 2
id: atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test
kind: claim
title: An exact five-row phase escape exists exactly when a finite quotient retains a rank-three bridge
distinct_from:
  atlas-exact-matrix-zero-set-is-a-finite-quotient-test: that treats the thirty A4 rows and q19243; this treats the five saturated rows and the weaker centrality word c19243, and also requires the linear phase energy to be positive.
  atlas-six-relator-quotient-identifies-h-bridge: that false target asks the universal quotient to kill every bridge; this classifies exact finite-matrix escapes by its finite quotients.
  atlas-five-row-operator-phase-lift: that is a uniform inequality for approximate matrices in all dimensions; this concerns only exact zeros at one finite dimension.
---

Let

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>.
```

The following are equivalent.

1. For some `k`, there is a relative unitary `U in U(20160k)` for which all
   six nonlinear defects vanish and

   ```text
   sum_(j in {0,11,30,44,55}) l_j(U)^2>0.             (SXFQ1)
   ```

2. `Gamma_6` has a finite quotient `F` in which both marked `A8` factors
   inject and at least one of the four standard `H=GL_3(2)` bridges survives.

If condition 2 holds, condition 1 may be realized in `Reg(F)`, with

```text
k=[F:A8].                                             (SXFQ2)
```

This exact equivalence does not decide the uniform approximate inequality.
In particular, absence of a finite quotient as in condition 2 would exclude
exact finite-dimensional escapes but would not provide a dimension-uniform
positive ratio in `(FPL4)`.

