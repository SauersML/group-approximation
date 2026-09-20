---
rg: 2
id: hrf-audit-projective-internality-does-not-round
kind: claim
title: Scalar projective Kazhdan models have exact internal commutants and uniform adjoint gap even when flexible rounding fails
distinct_from:
  kazhdan-commutants-are-internal: that is Liu's theorem for every Kazhdan ultraproduct homomorphism; this proves exact original-coordinate internality for scalar projective lifts directly and shows that this stronger lifting behavior does not imply representation stability.
  at-op62-holds-for-representation-lifts: that assumes genuine group representations at each coordinate; this permits nontrivial scalar multipliers and supplies nonroundable examples.
  rf-kazhdan-group-not-flexibly-hs-stable: that constructs nonroundable affine symplectic models; this identifies the exact uniform adjoint spectral gap and internal coordinate centralizers those models already possess.
artifacts:
  - research/artifacts/hyperbolic-rf-stability-audit-2026-09-20.md
---

**ESTABLISHED.** Let `Gamma` be finitely generated Kazhdan with a finite Kazhdan
pair `(F,kappa)`. Suppose `alpha_n:Gamma->U(d_n)` are scalar-projective
representations, with scalar multipliers tending pointwise to one. Let
`C_n=alpha_n(Gamma)' cap M_{d_n}` and let `E_n` be the trace-preserving conditional
expectation onto `C_n`. Then, for every matrix `x`,

```
||x-E_n(x)||_2 <= kappa^{-1} max_{g in F} ||[x,alpha_n(g)]||_2.
```

Consequently, for every nonprincipal ultrafilter and the induced homomorphism
`pi=[alpha_n]`,

```
pi(Gamma)' cap prod_omega M_{d_n} = [C_n]_omega.
```

Nevertheless there are such sequences that do not round flexibly. The scalar
projective affine-symplectic models of `rf-kazhdan-group-not-flexibly-hs-stable`
are instances. They even have operator-norm multiplicative defects tending to
zero and the regular limiting trace.

**Scalar-expander strengthening.** There also exist such nonroundable sequences
with `C_n=C I` for every `n`, dimensions tending to infinity, and the same
uniform gap. To obtain these, choose any irreducible constituent of each central
eigenspace model in the affine-symplectic example. These smaller sequences are
still scalar-projective and nonroundable, but a regular limiting trace is not
asserted for them. Thus even scalar expansion for the original generators does
not imply rounding.

Thus exact internality of the original coordinate commutants, uniform adjoint
gap, and Liu internality by themselves do not prove flexible HS stability. This
does not refute the separate GHB7 one-edge absorption hypothesis: the example
here contains `Z^2` and is not hyperbolic.

DERIVATION
hrf-audit-projective-internality-proof
