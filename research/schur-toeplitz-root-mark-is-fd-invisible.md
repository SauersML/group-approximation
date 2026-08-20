---
rg: 2
id: schur-toeplitz-root-mark-is-fd-invisible
kind: claim
title: The Schur Toeplitz root mark is nontrivial but invisible in every finite-dimensional unitary representation
artifacts:
  - research/artifacts/schur-toeplitz-root-defect-envelope-2026-08-20.md
distinct_from:
  steinberg-cover-fd-triviality: that kills every root over the simple binary Leavitt algebra; this Toeplitz packet envelope has finite quotients and kills only the designated forbidden root.
  fd-invisibility-of-compression: that identifies two subgroup images over Laurent polynomial quotients; this kills one explicit root because directly finite quotients erase its prescribed defect coefficient.
  parity-headed-compressor-kills-mark-in-exact-matrix-models: that compares nested commutants; this uses characteristic-p root torsion and finite-quotient direct finiteness.
---

Let `R_f` and `P_f` be as in
`schur-idempotent-is-an-injective-toeplitz-defect`, let `p=char(k)`, put
`Gamma_f=EL_5(R_f)`, and let `alpha` be the injective endomorphism induced by
`schur-toeplitz-envelope-has-proper-self-embedding`. Define

```text
H_f=<Gamma_f,t | t g t^-1=alpha(g), g in S_Gamma>,
w_f=x_12(P_f).                                             (STR1)
```

Then `H_f` is finitely presented, `w_f!=1`, and every finite-dimensional
unitary representation `rho:H_f->U(d)` satisfies

```text
rho(w_f)=1.                                                 (STR2)
```

Indeed each root subgroup is a copy of the elementary abelian `p`-group
`(R_f,+)`. Its image under `rho` is a finite simultaneously diagonalizable
group, so the intersection `A` of the kernels on the twenty root subgroups
has finite additive index. The two-sided ideal `I=R_f A R_f` contains `A`,
hence `R_f/I` is finite. Steinberg commutator relations and two spare indices
put every `x_ij(I)` in `ker(rho)`. By
`schur-idempotent-is-an-injective-toeplitz-defect`, the finite quotient
`R_f/I` kills `P_f`; hence `P_f in I` and `(STR2)` follows.

The root element is the nonidentity elementary matrix `1+E_12P_f` in the
base. The base embeds in the ascending HNN extension because `alpha` is
injective, so it remains nontrivial in `H_f`. Finite presentation follows
from finite presentation of `R_f` and `EL_5(R_f)`, plus one stable letter and
one conjugacy relation for each fixed base generator.

Thus `(H_f,w_f)` is an explicit relative minimally-almost-periodic pair whose
distinguished word is exactly the nonlinear Schur orientation. The remaining
question is not exact representation theory but whether `(STR2)` survives
normalized-HS asymptotic representations.
