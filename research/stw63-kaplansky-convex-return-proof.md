---
rg: 2
id: stw63-kaplansky-convex-return-proof
kind: route
title: Combine bidual uniqueness with Kaplansky density and Hahn--Banach
target: stw63-convex-unitary-return
requires:
  - stw63-all-von-neumann-codomains-have-uniqueness
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Regard `B**` as the von Neumann algebra in the universal representation of
`B`.  Fix finite `F subset Z` and `epsilon>0`.  Universal von Neumann
uniqueness gives `w in U(B**)` such that

```text
max_(a in F) ||w phi(a)w^* - psi(a)|| < epsilon/2.       (2)
```

We need one precise density fact.  Kaplansky, *A theorem on rings of
operators*, Pacific Journal of Mathematics 1 (1951), Theorem 1, proves that
the norm unit ball of a strongly dense star algebra is strongly dense in the
norm unit ball of its closure.  Its unitary consequence follows without an
extra lifting hypothesis: write `w=exp(ih)` for a bounded self-adjoint
`h in B**` (bounded Borel argument functional calculus), use the self-adjoint
part of Kaplansky density to approximate `h` strongly by a norm-bounded net
`h_j in B_sa`, and apply strong continuity of bounded continuous functional
calculus.  Thus there are `v_j in U(B)` with `v_j->w` strongly.  Since all
terms are unitary, also `v_j^*->w^*` strongly, and hence

```text
(v_j phi(a)v_j^*)_(a in F) -> (w phi(a)w^*)_(a in F)    (3)
```

strongly coordinatewise.

Every member of `B*` extends canonically to a normal functional on `B**`.
Let `C` be the convex hull in the finite Banach direct sum
`X=directSum_(a in F) B` of the vectors on the left of (3), and let
`y=(psi(a))_(a in F)`.  We claim

```text
distance_X(y,C) <= ||y-(w phi(a)w^*)_(a in F)|| < epsilon/2.   (4)
```

Indeed, if (4) failed, Hahn--Banach separation would give `f in X*` whose
real part separates `y` from `C` by more than the right side.  Extend its
finitely many coordinate functionals normally to `B**` and pass to the net
in (3).  The same strict separation would then hold between `y` and the
bidual vector `(w phi(a)w^*)_(a in F)`, contradicting the norm bound in (2).
Thus a finite convex combination from `C` lies within `epsilon` of `y`.
Interchanging `phi` and `psi` proves the second inclusion in (1).

Notice that the bidual vector need not lie in `X`; the separation argument,
not a false assertion of norm approximation to that bidual vector, is what
proves (4).

The convexification is essential to this argument: neither Kaplansky
density nor Hahn--Banach selects one `v_j` with small operator-norm error.
