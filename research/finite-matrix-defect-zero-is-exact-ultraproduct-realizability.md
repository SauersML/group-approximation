---
rg: 2
id: finite-matrix-defect-zero-is-exact-ultraproduct-realizability
kind: claim
title: A finite matrix defect has infimum zero exactly when its zero set exists in a tracial matrix ultraproduct
distinct_from:
  atlas-rankwise-gap-is-ultraproduct-obstruction: that is the Atlas packet's specialized rank/multiplicity instance; this is the dimension-free compactness theorem for every finite unitary polynomial-and-trace packet.
  exact-code-prefixes-have-matrix-ultraproduct-model: that diagonalizes exact realizations of growing code prefixes; this allows approximate realizations in arbitrary dimensions and identifies their global infimum with one exact ultraproduct realization.
  nonhyperlinear-group-has-finite-canonical-microstate-witness: that applies compactness to canonical group multiplication and trace data; this is the general finite noncommutative-polynomial engine behind that application.
artifacts:
  - research/artifacts/universal-hilbert-schmidt-obstruction-integration-2026-08-22.md
---

**ESTABLISHED.**  Fix finitely many noncommutative star-polynomials
`p_1,...,p_r,q_1,...,q_s` in unitary variables `X_1,...,X_m` and target
scalars `beta_1,...,beta_s`.  For `U in U(d)^m`, put

```text
E_d(U)=max( max_i ||p_i(U)||_(2,d),
            max_j |tr_d(q_j(U))-beta_j| ).              (FUZ1)
```

Then the following are equivalent.

```text
inf_(d>=1) inf_(U in U(d)^m) E_d(U)=0;                 (FUZ2)
```

```text
some tracial matrix ultraproduct contains unitaries u_1,...,u_m
with p_i(u)=0 and tau(q_j(u))=beta_j for every i,j.    (FUZ3)
```

For `(FUZ2) -> (FUZ3)`, choose a tuple with error below `1/n` and pass to
any free ultrafilter.  Polynomial `2`-norm errors vanish in the tracial
quotient and the normalized traces converge to the prescribed scalars.
For `(FUZ3) -> (FUZ2)`, choose unitary representatives.  Exactness says that
the set of coordinates on which all of the finitely many errors are below
any prescribed `epsilon>0` belongs to the ultrafilter, hence is nonempty.

Consequently, if `(FUZ3)` is impossible in every tracial matrix
ultraproduct, then there is one `c>0`, independent of dimension, such that

```text
E_d(U)>=c                         for every d and U.     (FUZ4)
```

This is rate-free: the dimensions may be adversarial and the errors may
converge arbitrarily slowly.  It also explains exactly why fixed-dimension
compactness is insufficient.  Positive minima `c_d` in each `U(d)^m` do not
exclude a diagonal escape unless `inf_d c_d>0`; absence of an ultraproduct
zero excludes that escape and is equivalent to the uniform positive gap.

