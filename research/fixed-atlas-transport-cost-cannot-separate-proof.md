---
rg: 2
id: fixed-atlas-transport-cost-cannot-separate-proof
kind: route
title: Evaluate the transport dual in the exact internal chart conjugacy
requires:
  - leavitt-factor-regular-charts-inner-conjugate
  - unitary-block-energy-transport
target: fixed-atlas-transport-cost-cannot-separate
---

Let `M=L(Q)` be the exact Leavitt group factor and let `W in M` be the
label-preserving internal chart conjugator from
`leavitt-factor-regular-charts-inner-conjugate`.  Every canonical atlas relator
holds exactly at `W`, so its packet defect is

```text
delta(W)=0.                                             (F1)
```

The two labelled copies of `C[A_8]` are trace-preserving, so their minimal
Wedderburn projections have exactly the regular weights `alpha_v,beta_u` used
in `(FTC1)`.

Apply `unitary-block-energy-transport` inside the finite factor `M`.  The block
energies

```text
m_(u,v)=||q_u W p_v||_2^2
```

form a transport plan with those marginals.  The assumed dual potentials
therefore give

```text
sum_(u,v) c_(u,v) ||q_u W p_v||_2^2 >= gamma > 0.     (F2)
```

But any universal estimate `(FTC2)` with `F(0)=0`, evaluated at the same exact
solution and using `(F1)`, gives the opposite bound

```text
sum_(u,v) c_(u,v) ||q_u W p_v||_2^2 <= 0,             (F3)
```

contradicting `(F2)`.  Hence the cost data that eventually separate finite
microstates cannot be one fixed tracially natural cost certificate; some
finite-rank/spectral selection step is mathematically necessary.
