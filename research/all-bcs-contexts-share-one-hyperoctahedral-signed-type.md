---
rg: 2
id: all-bcs-contexts-share-one-hyperoctahedral-signed-type
kind: claim
title: Every finite BCS context admits one common hyperoctahedral signed type
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  every-boolean-predicate-has-a-character-free-finite-type-block: that chooses a finite group and irreducible type separately for each predicate; this puts every context of one finite BCS in copies of one group and one irreducible type, with equal corner trace and explicit equal-rank coordinate atoms.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that still has to identify shared marginals after the context blocks enter one infinite algebraic corner; this solves only the uniform local finite-type normalization.
---

Let `B` be a finite BCS with nonempty allowed sets `R_c`.  Put

```text
L=lcm_c |R_c|,                 D=2L,
K_D=(C_2)^D semidirect S_D,                                  (HST1)
```

where `S_D` permutes the `D` sign coordinates, and let `rho_D` be the
tautological signed-permutation representation on `C^D`.  Then `rho_D` is
irreducible and has dimension greater than one.

For every context `c`, identify the coordinate set `[D]` with

```text
Omega_c=R_c times [D/|R_c|].                                (HST2)
```

For `x in U_c`, let `d_(c,x)` be the diagonal element of `(C_2)^D` whose
entry at `(a,j)` is `a_x`.  These are commuting involutions and their joint
spectrum on `rho_D` is exactly `R_c`; the atom belonging to `a` has rank
`D/|R_c|`.

Let `q_D=z_(rho_D)` be the primitive central block projection in `C[K_D]`.
For the `D` coordinate characters `chi_i` of `(C_2)^D`, the projections

```text
e_i=q_D e_(chi_i),             i=1,...,D,                   (HST3)
```

are algebraic, orthogonal, nonzero, and sum to `q_D`.  In the `rho_D` block
they are the coordinate rank-one projections.  Hence every context partition
is a sum of one common number `D` of rank-one signed-corner atoms, all context
copies have the same finite group and type, and

```text
tau_K_D(q_D)=D^2/|K_D|>0.                                  (HST4)
```

Every scalar character annihilates `q_D`.  Thus varying local group sizes,
irreducible dimensions, and corner traces are not part of the signed-Hecke
compatibility problem.  The sole remaining algebraic issue is how distinct
copies of this common block acquire equal shared-variable marginals in one
infinite group corner.
