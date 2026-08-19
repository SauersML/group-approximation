---
rg: 2
id: atlas-two-s3-energy-ceiling-below-19243-floor
kind: claim
title: The robust A4 atlas packet keeps two-generator S3 covariance energy strictly below the 19243 floor
artifacts:
  - research/artifacts/a4-hs-regularity-compiler-2026-08-19.md
distinct_from:
  atlas-two-s3-covariance-collapse: that asks the two covariance defects to vanish; this only asks for any asymptotic upper bound strictly below the packet-forced value 1/128.
  atlas-packet-forces-two-s3-covariance-energy: that supplies the opposite lower bound directly from collision-19243 centrality.
---

Use the canonical regular-`A8` relative-unitary model and the two fixed
`S_3=<h_a,h_b>` covariance defects

```text
a(U)=||U rho(h_a) U^*-rho(h_a)||_2,
b(U)=||U rho(h_b) U^*-rho(h_b)||_2.
```

There are constants

```text
eta < 1/128,
delta_0 > 0
```

such that every finite model with canonical atlas defect

```text
delta(U)=max_(s in bar_S)||pi_U(s)-1||_2 < delta_0
```

satisfies

```text
a(U)^2+b(U)^2 <= eta.                                  (A4-S3-CEIL)
```

The numerical target is deliberately much weaker than covariance collapse.
Any strict ceiling below `1/128` is enough; no rate and no convergence to zero
is required.

By `involution-covariance-is-four-times-binary-consistency`, this is exactly a
finite agreement-test target.  If `D_a,D_b` are the tracial consistency defects
between the two binary spectral PVMs of the two chart copies of `h_a,h_b`, then

```text
a^2+b^2=4(D_a+D_b).
```

Hence it is enough to prove the fixed numerical inequality

```text
D_a+D_b < 1/512                                        (A4-CONS-CEIL)
```

at sufficiently small atlas defect.

## Attempts

- **Exploit the thirty robust A4 cores, not a global chart perturbation.**
  `atlas-a4-packet-hs-regular-cores` says every shortest triangle is regular
  off a vanishing local residual.  The missing step is only to aggregate those
  local regular pieces strongly enough to control the two named `S3`
  directions.
- **Agreement-test formulation.**  Regard the thirty A4 contexts as a finite
  synchronization/unique-games instance on multiplicity spaces.  Local
  exactifications supply the labels; overlap disagreement is the consistency
  defect.  The exact binary identity above means the required global agreement
  budget is now the concrete constant `1/512`.
- **Use finite expansion, not a classical alignment.**  External multiplicity
  can mix locally valid sectors.  A successful argument should bound the two
  binary consistency defects through an expansion/Poincare inequality on the
  finite context-overlap graph.  This is compatible with operator-valued local
  labels and does not require selecting one automorphism sector.
- **Only beat the threshold.**  The old target `a^2+b^2->0` spends far more
  rigidity than the contradiction needs.  Even a coarse certificate such as
  `D_a+D_b<=1/1024` would close the hyperlinearity problem through the
  packet-only 19243 lower wall.
