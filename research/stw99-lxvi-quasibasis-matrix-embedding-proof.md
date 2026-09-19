---
rg: 2
id: stw99-lxvi-quasibasis-matrix-embedding-proof
kind: route
title: Encode ambient left multiplication in one matrix corner over the finite core
target: stw99-lxvi-finite-index-car-envelopes-are-stably-finite
requires:
  - stw99-lxvi-injective-limits-cannot-create-instability
artifacts:
  - research/artifacts/stw99-lxvi-coherent-car-no-go-audit-2026-08-30.md
---

Choose a finite Watatani quasi-basis `u_1,...,u_r in A` for `E`.  Thus, for
every `x in A`,

```text
x=sum_i u_i E(u_i^*x)=sum_i E(xu_i)u_i^*.                 (1)
```

Define matrices over `D` by

```text
p_(ij)=E(u_i^*u_j),
rho(a)_(ij)=E(u_i^* a u_j).                               (2)
```

The first identity in (1), applied to each `u_j`, gives

```text
(p^2)_(ij)
 =sum_k E(u_i^*u_k)E(u_k^*u_j)
 =E(u_i^* sum_k u_k E(u_k^*u_j))
 =p_(ij).
```

Also `p^*=p`, so `p` is a projection in `M_r(D)`.  The same calculation,
with `a u_j` in place of `u_j`, gives `p rho(a)=rho(a)`; applying (1) to
`u_j` after left multiplication by `a` gives `rho(a)p=rho(a)`.  Hence

```text
rho(a) in p M_r(D) p.                                     (3)
```

For `a,b in A`, insert the quasi-basis expansion of `b u_j` to obtain

```text
(rho(a)rho(b))_(ij)
 =sum_k E(u_i^*a u_k)E(u_k^*b u_j)
 =E(u_i^*ab u_j)
 =rho(ab)_(ij).
```

The expectation is star preserving, so `rho(a^*)=rho(a)^*`, and
`rho(1)=p`.  Thus

```text
rho:A->p M_r(D) p                                         (4)
```

is a unital star homomorphism, where the corner has unit `p`.

This representation is faithful.  If `rho(a)=0`, then every quasi-basis
coefficient of every `a u_j` vanishes, and (1) gives `a u_j=0` for all `j`.
Expanding the unit by (1) now gives

```text
a=a sum_j u_j E(u_j^*)=0.                                 (5)
```

Because `D` is stably finite, every matrix algebra over `D` is finite, and
so is every matrix amplification of the corner `pM_r(D)p`.  Amplifying the
faithful unital map (4) shows that every matrix algebra over `A` is finite.
Therefore `A` is stably finite.

For a finite group action `alpha:G actson D`, the canonical expectation
from `D crossed_product_alpha G` onto `D` has the implementing unitaries
`(v_g)_(g in G)` as a finite quasi-basis, so the first construction class in
the claim is excluded.  Repeated application gives the finite-tower case.
Every stage in an injective system of such towers is stably finite, and
`stw99-lxvi-injective-limits-cannot-create-instability` gives the last case.

Applied to an embedded CAR algebra, (4) explains the coherence obstruction:
finite module index compresses all ambient multiplication into one fixed
matrix level over the entire coherent dyadic tower.  Matrix instability
cannot then appear outside that tower.
