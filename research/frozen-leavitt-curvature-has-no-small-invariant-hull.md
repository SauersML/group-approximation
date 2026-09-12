---
rg: 2
id: frozen-leavitt-curvature-has-no-small-invariant-hull
kind: claim
title: Exact regular Leavitt factors permit rank-four certificate curvature with a macroscopic invariant hull
distinct_from:
  normalized-hs-tangent-quotient-is-nonabelian: That uses unrestricted sparse near-identity unitaries; this preserves both exact frozen finite-factor profiles, realizes curvature in the actual certificate word j squared, and bounds its invariant hull under two unchanged actors.
  two-kazhdan-correction-has-quadratic-rank-curvature: That supplies concentrated residuals under an all-unitary H2 hypothesis but no invariant support; this explicit frozen-factor construction shows that small reducing containment does not follow from the factor profiles and one concentrated certificate residual.
  leavitt-has-an-explicit-finite-c-killing-certificate: That excludes exact models of all nine words retaining the coordinate cycle; this studies one of those words inside exact factor models and makes no assertion that their full nine-word defects tend to zero.
artifacts:
  - research/artifacts/frozen-leavitt-pauli-curvature-and-saturation-2026-09-08.md
---

There are dimensions `n=24k -> infinity` and homomorphisms
`pi:P=C_3*C_2^3 -> U(n)` whose restrictions to both finite factors
are exactly regular multiples, with the following properties.

For the actual nine-word certificate relator `rho_1=j^2`,

```text
pi(rho_1)=I-2P_n,       rank(P_n)=4,
delta_n:=||pi(rho_1)-I||_2=4/sqrt(n),
||pi(rho_1)-I||_1=8/n,  tr(P_n)=delta_n^2/4.
```

Every orthogonal projection `E` containing `P_n` and commuting with the
two unchanged matrices `pi(c),pi(b_1)` has

```text
rank(E) >= n/12.
```

This absolute lower bound persists after arbitrary direct-sum padding
whose `c,b_1` actors retain the original summand. In particular padding
by `o(n)` dimensions cannot produce an `o(n)` reducing support containing
the original curvature.

Here `delta_n` measures only `rho_1`, not the maximum of all nine
certificate defects. No full nine-word microstate sequence is constructed.
Undoing the displayed rotation removes this one residual at generator
cost `delta_n/2`, so the example does not refute actor-changing repair.
