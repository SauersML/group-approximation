---
rg: 2
id: exact-codensity-no-matricial-rcc-proof
kind: route
title: Finitary alternating factor proves the exact-co-density RCC no-go
target: exact-codensity-does-not-imply-matricial-rcc
requires: []
artifacts:
  - research/artifacts/sl3-projective-rcc-audit-2026-08-21.md
---

Let `D=A_fin`, the union of the finite alternating groups acting on the
first `n` points. It is countable, locally finite, amenable, infinite,
simple, and perfect. If `sigma:D->U(d)` were nontrivial, simplicity would
make it faithful. It would then embed `A_n` into `U(d)` for every `n`.
Jordan's theorem gives a constant `J(d)` such that every finite subgroup of
`GL_d(C)` has an abelian normal subgroup of index at most `J(d)`. For
`n>=5`, simplicity of `A_n` makes that abelian normal subgroup trivial, so
`|A_n|<=J(d)`, impossible for unbounded `n`. Thus every finite-dimensional
unitary representation of `D` is trivial.

Set `C=SL_3(Z)` and `A=C x D`. The group `C` is finitely generated,
perfect, and Kazhdan. For every finite-dimensional unitary representation
`rho` of `A`, the restriction to `D` is trivial, so `rho(A)=rho(C)`.
The group `A` is hyperlinear: `C` is residually finite, `D` is amenable, and
hyperlinearity is preserved by direct products.

Choose noncommuting `x,y in D`. In

```text
L(A)=L(C) tensor_bar L(D),
```

put `u=1 tensor lambda_D(x)` and `h=(1,y)`. Then `u` belongs to the
commutant of the canonical copy of `C`, but

```text
[u,lambda_A(h)] = 1 tensor lambda_D([x,y]).
```

Since `[x,y]` is nontrivial, the canonical group trace of this commutator is
zero. Consequently

```text
1-|tau([u,lambda_A(h)])|^2 = 1.
```

As `A` is hyperlinear, its canonical trace embeds into a tracial matrix
ultraproduct, carrying this exact relative-commutant leak with it. This
proves the claim.
