---
rg: 2
id: kt-extrinsic-c-seam-has-a-finite-satisfiability-criterion
kind: claim
title: An extrinsic Kun--Thom seam correction is equivalent to one finite-packet approximate coboundary test
distinct_from:
  kt-c-normalization-seam-is-a-relative-commutant-cocycle: that identifies the exact cocycle equation assuming a relative-commutant gauge; this removes exact commutation as an input by a saturation criterion and includes the external SL3 relators.
  kt-internal-c-seam-has-a-kazhdan-gap: that gives a uniform negative answer inside the canonical AFP algebra; this characterizes exactly what new approximate solutions an embedding into `R^omega` must create.
  kun-thom-finitary-action-lifts-to-normalizer: that asks for the complete quotient actor; this criterion closes precisely the first C-normalization stage and does not assert that the remaining quotient kernel vanishes.
---

**ESTABLISHED SATISFIABILITY CRITERION.**  Fix a trace-preserving embedding

```text
iota:M=R rtimes P_A -> R^omega
```

and identify the embedded copy of `R` with the diagonal one.  Let `T` be a
finite generating set of `Gamma`, let `X=(x_j)_(j>=1)` be a countable
2-norm-dense subset of the unit ball of `R`, and choose a finite presentation
of `S=SL_3(Z)` on the generators `A,C`, with relator set `Rel_S`.

There is a unitary `z in R' cap R^omega` such that

```text
z v_gamma=rho_gamma z                         (gamma in T),
r(u_A,z u_C)=1                                (r in Rel_S)    (KES1)
```

if and only if for every `n>=1` there is a unitary `z_n in R^omega` with

```text
max_(j<=n) ||[z_n,x_j]||_2 <1/n,
max_(gamma in T) ||z_n v_gamma-rho_gamma z_n||_2 <1/n,
max_(r in Rel_S) ||r(u_A,z_n u_C)-1||_2 <1/n.           (KES2)
```

Thus the first extrinsic correction is a fixed finite group packet plus an
exhausting commutant test; there is no hidden choice of subgroup embeddings.
Property `(T)` makes the seam part quantitatively rigid, while countable
saturation converts arbitrarily accurate solutions of `(KES2)` into an
exact solution.

The criterion also states the precise positive/negative fork.  A positive
construction must produce `(KES2)` for some CE embedding of the AFP paste.
A uniform lower bound for `(KES2)` over every such embedding would prevent
the first mixed correction and hence refute the full normalizer lift.  Mere
McDuffness or diffuseness of `R' cap R^omega` is insufficient: the equations
test invariant vectors for the specific Kazhdan action
`Ad(rho_gamma)` and the simultaneous finite `SL_3(Z)` holonomy.

DERIVATION
kt-extrinsic-c-seam-saturation-proof
