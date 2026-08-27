---
rg: 2
id: dense-transitive-action-has-no-nontrivial-finite-factor-proof
kind: route
title: Close a finite arithmetic factor under the ambient p-adic group and use transitivity
target: homogeneous-k-orbit-factor-has-no-finite-a-refinement
requires: []
---

Let `D subset L^infinity(X)` be finite-dimensional and `A`-invariant.  The
Koopman representation of `L` on `L^2(X)` is strongly continuous.  Since
`A` is dense in `L` and `D` is finite-dimensional, hence `L^2`-closed, for
`ell in L` and any sequence `a_j -> ell` in `A` we have

```text
u_(a_j) D = D,  u_(a_j) xi -> u_ell xi  (xi in D),
```

so `u_ell D subset D`; applying the same argument to `ell^-1` gives equality.
Thus `D` is `L`-invariant.

The minimal projections of `D` form a finite measurable partition on which
`L` acts continuously by permutations.  The kernel of the resulting map
`L -> Sym(m)` is an open finite-index normal subgroup.  The groups
`SL_n(Q_p)`, `n>=2`, have no nontrivial finite continuous quotient, so the
permutation action is trivial.  Transitivity, hence ergodicity, of the left
`L`-action on `L/Lambda'` then makes every minimal projection constant; thus
`D=C`.

On the other hand density of `C` in `K` gives
`L^infinity(X)^C=L^infinity(X)^K`, whose atoms are the `r` distinct
`K`-orbits.  For `r>=2` this algebra is non-scalar, so it cannot lie in an
`A`-invariant finite-dimensional `D`.  A finite equivariant refinement would
generate exactly such a `D`, proving the claim.
