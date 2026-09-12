---
rg: 2
id: huge-elementary-abelian-two-group-proof
kind: route
title: Compare cardinality, then check the elementary abelian structure coordinatewise
target: huge-elementary-abelian-two-group-is-not-sequential-operator-mf
requires:
  - sequential-operator-mf-continuum-cardinality-bound
---

Every element of `E_I` has finite support.  For infinite `I`, the set of
finite subsets of `I` has cardinality `|I|`, and each support carries only
finitely many binary functions.  Thus

```text
|E_I|=|I|>continuum,
```

so the sequential cardinality ceiling excludes `IsOperatorMF E_I`.

Coordinatewise addition over `F_2` makes the group abelian of exponent two.
Every finitely generated subgroup is supported on a finite union of finite
supports and is therefore a finite elementary abelian group; hence `E_I` is
locally finite and amenable.

If `x!=0`, choose `i` in its support.  The coordinate map `E_I->C_2`
separates `x`, proving residual finiteness.

Finally, a Kazhdan set in a discrete group is finite.  Given any finite
`Q subset E_I`, choose `i` outside the union of its supports.  The nontrivial
character

```text
chi_i(x)=(-1)^(x(i))
```

fixes every element of `Q` exactly but has no nonzero globally invariant
vector.  Therefore no finite Kazhdan set exists.
