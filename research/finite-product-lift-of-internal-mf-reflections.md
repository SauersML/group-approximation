---
rg: 2
id: finite-product-lift-of-internal-mf-reflections
kind: claim
title: Finite block diagonals lift heterogeneous internal MF reflections
root: true
artifacts:
  - research/finite-product-lift-of-internal-mf-reflections-proof.md
---

Let `U=L_(F_2)(1,2)^x`.  For `1<=i<=m`, let `K_i<=U` and let
`pi_i:K_i->>Q_i` induce natural bijections

```text
Hom(Q_i,M)~=Hom(K_i,M)                                  (FPL1)
```

for every MF group `M`.  Then the binary Leavitt matrix self-similarity gives
an internal embedding

```text
K=product_i K_i<=U.                                     (FPL2)
```

For `Pi=product_i pi_i:K->>product_i Q_i`, precomposition induces

```text
Hom(product_i Q_i,M)~=Hom(K,M)                          (FPL3)
```

naturally for every MF group `M`.  Therefore

```text
Rad_MF(K)=Pi^(-1)(Rad_MF(product_i Q_i)),                (FPL4)

cl_MF^K(N)=Pi^(-1)(cl_MF^(product_i Q_i)(Pi(N)))         (FPL5)
```

for every normal subgroup `N` of `K`.  If every `Q_i` is MF, then

```text
Rad_MF(K)=product_i ker(pi_i).                           (FPL6)
```

If `ker(pi_i)` is normally generated in `K_i` by `d_i`, the radical in
`(FPL6)` is normally generated in `K` by the `m` coordinate elements `d_i`.
If every `K_i` is finitely generated, so is `K`.

The same theorem holds simultaneously for finite, compact,
finite-dimensional unitary, and finite-dimensional linear targets over each
field whenever `(FPL1)` holds for that class.
