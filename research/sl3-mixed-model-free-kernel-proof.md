---
rg: 2
id: sl3-mixed-model-free-kernel-proof
kind: route
title: Compute the Bass--Serre fold kernels and let an atomic quotient sector supply only quotient faithfulness
target: sl3-mixed-model-hard-part-is-free-kernel
requires:
  - hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower
  - sl3-arithmetic-double-finite-representations-fold
  - sl3-overlap-full-in-fd-ambient-images
---

## 1. The two kernels are free of infinite rank

The fold `q_D` is injective on each vertex group of `D=A*_C A`.  Therefore
`K_D` meets every conjugate of a vertex stabilizer in the Bass--Serre tree
trivially, so `K_D` acts freely and is a free group.  Since `K_D` is normal
with quotient `A`, the quotient graph has two vertices and edge set

```text
K_D\D/C ~= A/C.
```

The cosets `h^n C`, for `h=diag(p,1,p^(-1))` and `n in Z`, are distinct, so
`A/C` is countably infinite.  The quotient graph is two vertices joined by
countably many parallel edges.  Hence `K_D~=F_infinity`.

For `H`, the quotient `q_H` is injective on every conjugate of its Bass--Serre
vertex group `A`, so `K_H` also acts freely on the HNN tree.  Modulo `K_H`
the vertices are indexed by

```text
(A x Z)/A ~= Z,
```

and between consecutive vertices there are the countably many edges indexed
by `A/C`.  Its fundamental group has countably infinite rank, proving
`K_H~=F_infinity`.

## 2. Atomic sectors factor through the quotients

The double statement is
`sl3-arithmetic-double-finite-representations-fold`.

For the HNN, let `rho:H->U(d)` be finite dimensional and put `T=rho(t)`.
The HNN relation says

```text
T in rho(C)'.
```

Apply `sl3-overlap-full-in-fd-ambient-images` to `rho|_A`.  It gives
`rho(C)'=rho(A)'`, hence `T` commutes with `rho(A)`.  Thus `rho` factors
through `q_H:H->A x Z`.  The assertion passes blockwise to every atomic
direct sum.

## 3. Kernel-faithfulness is exactly enough

Both quotients `A` and `A x Z` are residually finite.  Choose a faithful
atomic homomorphism

```text
alpha:q(G)->U(R_0)
```

obtained from a separating family of finite quotients, represented with
positive summable trace weights in a hyperfinite finite algebra `R_0`.

Suppose `psi:G->U(M)` is injective on `K=ker(q)`.  Define

```text
Phi(g)=alpha(q(g)) direct_sum psi(g)
```

in the Connes-embeddable algebra `R_0 direct_sum M`.  If `Phi(g)=1`,
faithfulness of `alpha` gives `q(g)=1`, so `g in K`; injectivity of
`psi|_K` then gives `g=1`.  Hence `Phi` is an abstract faithful embedding.
Embed the Connes-embeddable algebra `R_0 direct_sum M` trace-preservingly
into a tracial matrix ultrapower.  The composite is an injective
homomorphism of `G` into that ultrapower's unitary group, so
`hyperlinear-iff-group-factor-embeds-in-hyperfinite-ultrapower` makes `G`
hyperlinear.

Conversely, a hyperlinear group has a faithful homomorphism into a tracial
matrix ultraproduct and its restriction to `K` is injective.  This proves
`(MFK2)`.

Finally, if a proposed mixed model has an atomic sector and another sector
`psi`, Step 2 says the atomic sector is identically one on `K`.  Therefore
faithfulness of the whole direct sum forces `psi|_K` to be injective.  This
is the claimed no-padding obstruction.
