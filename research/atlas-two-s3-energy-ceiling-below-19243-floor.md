---
rg: 2
id: atlas-two-s3-energy-ceiling-below-19243-floor
kind: claim
title: The robust A4 atlas packet keeps two-generator S3 covariance energy strictly below the 19243 floor
artifacts:
  - research/artifacts/a4-hs-regularity-compiler-2026-08-19.md
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
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
D_a+D_b < 1/512.                                       (A4-CONS-CEIL)
```

at sufficiently small atlas defect.

## Attempts

- **First compile away all approximate local group laws.**
  `atlas-a4-context-network-simultaneous-hs-exactification` turns the two A8
  charts plus all thirty A4 contexts into one exact representation of a fixed
  virtually-free graph of finite groups.  The non-tree stable letters remain
  `o(1)` from identity.  Thus the remaining theorem may be attacked entirely
  on exact finite-group representation data plus a finite set of small
  holonomy matrices; there is no need to coordinate thirty independent
  Gowers--Hatami perturbations.
- **Use the integer representation cone.**  In a graph of finite groups the
  vertex irreducible multiplicity vectors satisfy finite linear restriction
  equations on the `C2/C3` edges, and every positive integer solution is
  realizable.  Normalize these vectors to a fixed rational polytope and search
  its faces for the worst binary consistency budget compatible with the
  collision-19243 centrality inequality.
- **Agreement-test formulation.**  Regard the exactified A4 contexts as a
  finite synchronization/unique-games instance on multiplicity spaces.
  Overlap disagreement is the consistency defect, and the exact binary identity
  above means the total budget to beat is the concrete constant `1/512`.
- **Use finite expansion, not a classical alignment.**  External multiplicity
  can mix locally valid sectors.  Bound the two binary consistency defects
  through an expansion/Poincare inequality on the finite context/edge graph,
  with the small stable-letter holonomies as the only continuous error terms.
- **Only beat the threshold.**  The old target `a^2+b^2->0` spends far more
  rigidity than the contradiction needs.  Even a coarse certificate such as
  `D_a+D_b<=1/1024` would close the hyperlinearity problem through the
  packet-only 19243 lower wall.
