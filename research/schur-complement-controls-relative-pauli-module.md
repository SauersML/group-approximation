---
rg: 2
id: schur-complement-controls-relative-pauli-module
kind: claim
title: Three controlled Schur-complement coefficients generate the forbidden relative-Pauli module
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that counts the whole difference of the two commutants; this exhibits a fixed three-coefficient submodule of that difference and retains every external multiplicity coordinate.
  adjoint-supertrace-cannot-pay-hs-selection-load: that rules out extracting matrix mass from one arbitrarily selected adjoint direction; this uses three canonical packet-algebra coefficients and takes their full right module over the packet commutant.
  regular-chart-wedderburn-coefficient-compiler: that exposes all coefficients of an arbitrary operator in a regular finite-group chart; this gives explicit coefficients intrinsic to the Schur-complement packet and computes the module they generate.
---

Let `M_f(x)=[[U_f(x),e_t],[e_s^T,0]]` be the affine Schur matrix and
`A_f<=B_f` its Schur--Clifford packet inclusion.  In the finite-dimensional
algebra `C[B_f]` let

```text
e_x=2^(-k) product_i (1+(-1)^(x_i) z_i)
```

be the central selector idempotent.  There are explicit self-adjoint
involutions

```text
P_f=sum_x e_x P_x,                 Q_f=sum_x e_x Q_x              (SCP1)
```

in `A_f' cap C[B_f]` such that

```text
[P_f,Q_f]=F_f,
F_f=sum_x (-1)^(f(x)) e_x.                                      (SCP2)
```

Thus `P_f,Q_f` commute on an allowed selector sector and form one relative
Pauli pair on a forbidden selector sector.  The construction uses only the
inverse of the always-invertible affine block `U_f(x)` and is effective for
every fixed predicate.

More strongly, let `rho` be any finite-dimensional representation of `B_f`
in the `J=-1` sector, and let `m_(x,lambda)` be its multiplicity of the
`B_f`-simple labelled by selector character `x` and radical character
`lambda`.  If `C_B=End_(B_f)(rho)` and `R_A,R_B` are the two adjoint Reynolds
projections, then the right `C_B`-module generated on the forbidden simple
blocks by

```text
P_f, Q_f, P_f Q_f
```

is contained in `range(R_A-R_B)` and has dimension

```text
3 sum_(x:f(x)=1,lambda) m_(x,lambda)^2.                           (SCP3)
```

Consequently the quadratic multiplicity part of the predicate Reynolds gap
has a fixed three-coefficient frame; no microstate-dependent choice of an
irreducible copy or of one low-energy adjoint vector is required.  The
remaining return problem is coefficient covariance/groupification, not
adjoint-basis selection.

