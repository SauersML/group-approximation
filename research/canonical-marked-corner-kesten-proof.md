---
rg: 2
id: canonical-marked-corner-kesten-proof
kind: route
title: Pass adjoint moments to the regular walk and apply Kesten's gap
target: canonical-marked-corner-nonamenable-density-vanishes
requires:
  - central-involution-corner-exactification
---

For `g in Lambda`, canonicality and
`<J> intersect Lambda=1` give

```text
tr_(e_n)(phi_n(g)|_(e_n H_n))->delta_(g,1).
```

The trace of an adjoint unitary is the squared modulus of the underlying
normalized trace.  Approximate multiplicativity on every fixed word
therefore implies that every polynomial moment of `A_n` converges to the
corresponding moment of

```text
A_reg=I-(1/|S|)sum_(s in S)lambda_Lambda(s).
```

Kesten's criterion for nonamenability gives
`spec(A_reg) subset [kappa,2]`.  Weak convergence of the compactly supported
spectral measures and Portmanteau then imply `(CMN1)` for `b<kappa`.

For `Q_n=1_[0,b](A_n)`, positivity gives

```text
tr_ad(R_nA_n)>=b tr_ad(R_n(1-Q_n))
              >=b(tr_ad(R_n)-tr_ad(Q_n)),
```

which is `(CMN2)`.

