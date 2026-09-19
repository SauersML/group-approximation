---
rg: 2
id: kt-extrinsic-seam-correctors-are-orthogonal-to-the-afp-paste
kind: claim
title: Every extrinsic Kun--Thom seam corrector is maximally orthogonal to the AFP paste
distinct_from:
  kt-canonical-afp-seam-has-no-internal-gauge-correction: that excludes a corrector belonging to the pasted algebra; this computes the conditional expectation and distance of every corrector in an arbitrary finite ambient extension.
  kt-passive-mcduff-amplification-does-not-close-the-seam: that rules out a spectator tensor enlargement; this applies to any ambient finite factor and quantifies how much genuinely new bimodule mass is required.
  kt-extrinsic-c-seam-has-a-finite-satisfiability-criterion: that characterizes existence by approximate equations; this gives a necessary geometric condition on every solution of those equations.
---

**ESTABLISHED EXTRINSICITY BOUND.**  Let the canonical AFP algebra
`M=R rtimes P_A` sit trace-preservingly in an arbitrary finite tracial von
Neumann algebra `D`.  If a unitary `z in R' cap D` satisfies

```text
z v_gamma=rho_gamma z                 (gamma in Gamma), (KEO1)
```

then

```text
E_M(z)=0,                  dist_2(z,M)=1.               (KEO2)
```

More generally, if `z in R' cap D` is unitary and

```text
delta=max_(gamma in Q)||zv_gamma-rho_gamma z||_2
```

for a Kazhdan pair `(Q,kappa)`, then

```text
||E_M(z)||_2 <= delta/kappa,
dist_2(z,M)^2 >= 1-(delta/kappa)^2.                     (KEO3)
```

Thus an asymptotic solution of the finite satisfiability criterion cannot be
a small perturbation of the AFP construction: its entire mass escapes into
a new relative Gamma-bimodule orthogonal to `L^2(M)`.  This is the exact
amount of new structure a positive embedding must create.

DERIVATION
kt-extrinsic-seam-orthogonality-proof
