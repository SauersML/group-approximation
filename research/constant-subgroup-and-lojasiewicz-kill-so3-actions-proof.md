---
rg: 2
id: constant-subgroup-and-lojasiewicz-kill-so3-actions-proof
kind: route
title: The constant elementary subgroup kills every SO(3) image
target: jacobson-projective-two-sheet-actions-collapse
requires:
  - bounded-dimension-jacobson-head-has-algebraic-collapse
---

Let

```text
K=EL_28(F_2)=GL_28(F_2) <= EL_28(J).
```

The group `K` is nonabelian simple. Indeed its center is trivial over
`F_2` and `PSL_n(F_2)` is simple for `n>=3`.

Let `phi:G->SO(3)` be a homomorphism. Its restriction to `K` is either
injective or trivial. The finite subgroups of `SO(3)` are cyclic,
dihedral, tetrahedral, octahedral, and icosahedral; their only nonabelian
simple member is `A_5`. Since `GL_28(F_2)` is not `A_5`, it cannot embed
in `SO(3)`. Therefore

```text
phi(K)=1.                                               (CSL1)
```

Fix `a in J`. Permutation matrices in `K` conjugate
`x_ij(a)` to `x_kl(a)` for arbitrary ordered pairs of distinct indices.
Equation `(CSL1)` implies that all these roots have one common image,
say `u_a`. Choose distinct `i,j,k`. The Steinberg relation gives

```text
x_ik(a)=[x_ij(a),x_jk(1)].
```

The second factor lies in `K`, so

```text
u_a=[u_a,1]=1.                                         (CSL2)
```

The elementary roots generate `G`. Hence `(CSL2)` proves that `phi` is
trivial.

It remains to make the exact statement uniform. The compact real
algebraic set

```text
X=SO(3)^Sigma
```

is cut out inside a Euclidean space by the orthogonality and determinant
equations. Let `F_R:X->R^m` list the real matrix entries of
`r(Q)-I` for all `r in R`. Word inversion is transpose on `SO(3)`, so
`F_R` is polynomial. The preceding argument proves

```text
F_R^(-1)(0)={(I)_(s in Sigma)}.                         (CSL3)
```

The semialgebraic Lojasiewicz inequality on the compact set `X` supplies
constants `C'<infinity` and `alpha>0` such that

```text
dist(Q,(I)_Sigma) <= C'||F_R(Q)||^alpha.                (CSL4)
```

All Euclidean, maximum, and normalized Hilbert--Schmidt norms on this
fixed finite product of three-by-three matrices are equivalent by fixed
constants. Absorbing them into `C'` turns `(CSL4)` into `(JPA1)`.

A weaker modulus also follows by compactness alone, but `(CSL4)` records
the useful power-law form. The argument applies only when the projective
coefficient rotations themselves satisfy the presentation relators.
For inequivalent carrier sheets,
`two-sheet-projective-closure-forces-equivalent-carriers` shows why the
full mixed tuple does not produce such a coefficient tuple.
