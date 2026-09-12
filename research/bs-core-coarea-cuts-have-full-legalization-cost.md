---
rg: 2
id: bs-core-coarea-cuts-have-full-legalization-cost
kind: claim
title: BS core spectral coarea cuts can have constant boundary and full legalization cost
distinct_from:
  long-bs14-packets-defeat-invariant-op-thresholding: that thresholds the difference of two close inequivalent exact cores and observes full invariant hull; this gives a direct projection/coarea obstruction inside one fixed exact core.
  bs14-periodic-koopman-modes-refute-skeleton-regularity: that constructs slow unitary Fourier modes in the base commutant; this constructs half-rank projections and computes the exact rank cost of replacing them by core-reducing cuts.
  gauge-optimized-section-energy-controls-flexible-repair: that asks for the full arithmetic nonlinear estimate; this rules out legalizing its spectral layers by a Poincare inequality for the exact BS core alone.
---

For `m>=2`, put `N_m=4^m-1` and `zeta_m=exp(2 pi i/N_m)`.  On the
basis indexed by `Z/m`, define

```text
R_m e_j=e_(j-1),       S_m e_j=zeta_m^(4^j)e_j.       (BCC1)
```

This is an irreducible exact `BS(1,4)` core.  Let `P_m` project onto a
cyclic interval of `floor(m/2)` consecutive basis vectors.  It is a
spectral projection of `S_m`, and

```text
[P_m,S_m]=0,              ||[P_m,R_m]||_F^2=2.        (BCC2)
```

The only projections reducing both generators are `0,1`.  Hence

```text
min_(Q in {R_m,S_m}', Q projection)
 ||P_m-Q||_F^2=min(floor(m/2),ceil(m/2)).              (BCC3)
```

Thus normalized core-invariance defect tends to zero while distance from
every legal core cut tends to `1/sqrt(2)`.  No dimension-independent core
Poincare/coarea inequality can legalize an approximately core-invariant
spectral layer at rank cost proportional to squared commutator energy.

This obstructs a proof method, not `(GOS1)`.  Endpoint property `(tau)` can
round after an endpoint representation is authenticated.  Before atom
selection only the amenable BS core acts, and `(BCC1)--(BCC3)` prevent
legalizing the truncation there.  A successful coarea proof must use the
two endpoint rows to charge these cuts while constructing the endpoint
action, rather than in a prior core-only step.

The first such endpoint-row test is positive.
`endpoint-triangle-charges-bs-sign-cut-volume` proves that, relative to any
authenticated exact same-core endpoint, multiplying its reflection by the
half-interval sign costs at least `2 floor(m/2)` in square-plus-first-cubic
Frobenius energy.  If the modified reflection remains an involution, the
first cubic alone costs at least `4 floor(m/2)`.  Thus `(BCC1)--(BCC3)` is
only a firewall against **prior** core legalization, not a low-energy full
endpoint counterpacket.

