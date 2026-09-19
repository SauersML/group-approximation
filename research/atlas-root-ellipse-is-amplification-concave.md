---
rg: 2
id: atlas-root-ellipse-is-amplification-concave
kind: claim
title: The A4 root ellipse is homogeneous concave in squared energies and cannot be diluted by amplification
distinct_from:
  atlas-a4-root-energy-ellipse-ceiling: that asks for a matrix-specific strict upper bound on approximate packet-collision models; this proves the opposite-direction permanence of any blockwise lower obstruction under direct sums.
  atlas-a4-finite-quotient-escape-fence: that produces a lower bound for one regular finite quotient; this upgrades the bound to arbitrary direct sums and convex mixtures of such quotient blocks.
---

For a nonnegative squared-energy vector

```text
e=(e_01,e_12,e_23,e_30)
```

put

```text
S(e)=2 sqrt(e_01)+2 sqrt(e_23)+4 sqrt(e_30),
F(e)=S(e)^2+S(e)sqrt(e_12)+e_12.                       (ROOT-CONC-1)
```

Then `F` is positively homogeneous and concave on the nonnegative orthant.
Consequently, for weights `theta_j>=0`, `sum_j theta_j=1`,

```text
F(sum_j theta_j e^(j)) >= sum_j theta_j F(e^(j)).      (ROOT-CONC-2)
```

The squared root energies of an orthogonal direct sum are exactly the
dimension-weighted averages of the squared root energies of its blocks.
Therefore `(ROOT-CONC-2)` is an amplification theorem: if every block has
root ellipse at least `c`, then every direct sum and external amplification
also has root ellipse at least `c`.

In particular, take any finite collection of nontrivial regular finite-quotient
models of the packet-collision quotient `Gamma_A4`.  Each block has `F>=1` by
`atlas-a4-finite-quotient-escape-fence`, hence every arbitrary
dimension-weighted direct sum satisfies

```text
F>=1.                                                  (ROOT-CONC-3)
```

The scalar constant one is sharp on the admissible binary energy patterns:
`e_12=1` and the other three coordinates zero gives `F=1`.  This is a
sharpness statement for the two-variable ellipse optimization.  By
`atlas-e12-binary-extremal-is-a-finite-residual-test`, realization by a group
quotient is exactly the finite-residual question for the omitted bridge
`w_12` in the three-bridge quotient `Q_12`; that question remains undecided.

Thus amplification cannot hide a finite-quotient countermodel to the proposed
`3/128` ceiling.  Any successful ceiling proof must exclude every nontrivial
finite quotient block before taking direct sums; convex dilution supplies no
escape from that requirement.
