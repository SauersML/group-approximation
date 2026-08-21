---
rg: 2
id: common-source-gram-saturation-proof
kind: route
title: Identify and prove sufficiency of the common source-Gram scalar
target: common-source-hnn-bridges-need-one-gram-saturation-identity
requires: []
---

Put `V_c=p_cU_cQ`.  Since `p_c,Q` are projections,

```text
tau(Q)-tau(V_c^*V_c)=||(1-p_c)U_cQ||_2^2.
```

Let `Q_c` be the spectral projection of `V_c^*V_c` for `[1/2,1]`.
Markov's inequality gives

```text
tau(Q-Q_c)<=2(tau(Q)-tau(V_c^*V_c)).
```

For `Q'=meet_c Q_c`, codimensions add, so

```text
tau(Q-Q')<=2 sum_c ||(1-p_c)U_cQ||_2^2.
```

Polar-rounding `V_cQ'` now produces partial isometries with the literal
common source `Q'`, at loss bounded by the same sum.  This proves
sufficiency of the scalar row.

It is not a consequence of the HNN edges.  If source edge type `sigma_c`
induces as `m_c pi_c + sum_(rho!=pi_c)m_(c,rho)rho`, the stable letter
transports the entire `sigma_c`-isotypic source while `p_c` retains only the
`pi_c` term.  Every other induced summand contributes exactly to the deficit
above.  Central signs and selector characters cannot delete all such
summands.  The regular finite-packet representation contains them with
positive Plancherel mass at zero relator defect, proving that ordinary edge
relations alone cannot yield saturation.
