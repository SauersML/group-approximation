---
rg: 2
id: disjoint-subgroups-force-flat-finite-phase-marginals
kind: claim
title: Trivially intersecting active and phase subgroups force flat phase marginals
artifacts:
  - research/disjoint-subgroup-flat-phase-factorization-proof.md
distinct_from:
  jacobson-d8-polar-has-flat-nine-phase-first-row: that computes the first row for one explicit residual polar; this is the subgroup-theoretic factorization theorem applying to every operator supported in the active reduced group algebra.
  qutrit-external-cyclic-router-selects-only-one-hidden-third: that leaves the active subgroup and obtains nonflat incidence through a nontrivial intersection line; this theorem explains exactly why such an extra line is necessary.
---

Let `Gamma` be a discrete group and let `F,M<=Gamma` satisfy

```text
F intersect M={1}.
```

Write `tau` for the canonical trace on `C*_r(Gamma)`. Then for every
`z in C[F]` and every `y in C*_r(M)`,

```text
tau(z y)=tau(z) tau(y).                                  (DF1)
```

Consequently, for every projection `p in C[F]` and every
`v in C*_r(M)`,

```text
||p v||_2^2=tau(p) tau(v v*),
||v p||_2^2=tau(p) tau(v* v).                            (DF2)
```

In particular, if `F` is finite abelian and `(p_chi)` are its character
atoms, then every operator supported in `C*_r(M)` has exactly flat one-sided
phase marginals:

```text
||p_chi v||_2^2=(1/|F|) tau(v v*)
```

for every `chi`. The same conclusion applies to a polar partial isometry
whenever that polar remains in `C*_r(M)`; this is automatic for the finite
active algebras used in the Jacobson residual calculations.

For the qutrit packet `C=<J,Z_1> isomorphic C_3^2` and the active subgroup
supporting the D8 residual polar, the established support calculation gives
`C intersect M={1}`. Hence flatness is not a coincidence of the displayed
polar formula: **no compression, linear combination, functional calculus,
or polar operation carried out entirely inside that active reduced group
algebra can select one qutrit phase over another.** Any Hall-deficient
continuation must introduce support whose subgroup meets the qutrit packet
nontrivially, or impose a genuinely joint relation between several such
external carriers.
