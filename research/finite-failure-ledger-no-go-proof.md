---
rg: 2
id: finite-failure-ledger-no-go-proof
kind: route
title: Decompose induced failure types and construct the saturated-capacity countermodel
target: finite-failure-ledgers-do-not-bypass-source-gram
requires: []
---

For finite `H<=G` and an irreducible `sigma`, write
`Ind_H^G(sigma)=directSum_rho m_rho rho`.  With central idempotents
`e_sigma,p_rho` and bridge `U`, the operators

```text
P_rho=e_sigma U^*p_rho Ue_sigma
```

are mutually orthogonal projections summing to `e_sigma`.  Their regular
trace weights are

```text
tau(P_rho)=d_sigma d_rho m_rho/|G|,
```

so unwanted types have honest positive canonical mass.

On the analytic source `Q<=e_sigma`, however,

```text
F_rho=QU^*p_rho UQ,   sum_rho F_rho=Q,
```

are merely positive effects.  They are a PVM exactly when `Q` commutes with
all transported type projections, which is already a source-reduction
hypothesis.

Even grant that hypothesis and route all failure projections into pairwise
orthogonal tagged ranges under a capacity `C`.  The resulting estimate is
only `sum_a tau(F_a)<=tau(C)+energy`.

For an exact zero-energy countermodel take `K=C_2 x C_2` in its regular
representation, with four primitive Fourier projections `e_c` of trace
`1/4`.  Set selected projections `p_c=1-e_c`, failures `F_c=e_c`, take
`C=1`, and route each failure by the identity with its own character tag.
All packet, tag, and route equations hold; the capacity inequality is an
equality, but

```text
meet_c p_c=0.
```

Thus the ledger neither creates an accepted carrier nor forces energy.
Only an independent source-saturation theorem or a capacity surplus tied to
the mark can close the argument.
