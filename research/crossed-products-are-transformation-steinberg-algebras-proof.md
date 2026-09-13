---
rg: 2
id: crossed-products-are-transformation-steinberg-algebras-proof
kind: route
title: Send f u_γ to the range-coordinate function on the sheet {γ} × X and compare convolutions
target: crossed-products-are-transformation-steinberg-algebras
requires: []
artifacts:
  - research/artifacts/un-blueprint-2026-09-13-part1.md
---

**Topology.**
- As a space `X ⋊ Γ = Γ × X`, with `Γ` discrete.
- The sheets `{γ} × U`, for `U` clopen, are compact open bisections: source and range restrict to the
  homeomorphisms `x |-> x` and `x |-> γx`.
- They form a basis, so `X ⋊ Γ` is Hausdorff and ample, with unit space `{e} × X = X`.

**The algebra.** `A_k(X ⋊ Γ)` is the `k`-module of locally constant compactly supported functions
`F : Γ × X -> k`. Compact support means `F` vanishes off finitely many sheets, and on each sheet it is
locally constant. The convolution is

```text
(F * G)(η, x) = sum over factorizations (γ, δx)(δ, x) = (η, x)  of  F(γ, δx) G(δ, x)
             = sum_δ F(ηδ^(-1), δx) G(δ, x).
```

**The map.** `Ψ(sum_γ f_γ u_γ)(γ, x) = f_γ(γx)`.
- `Ψ` is `k`-linear.
- It is bijective. On the sheet `{γ} × X` it is the bijection `LC(X,k) -> LC(X,k)`, `f |-> f o γ`.
  Compact support in `A_k` is exactly finiteness of the sum.

**Multiplicativity.** In the skew group ring, `(f u_γ)(g u_δ) = f · (g o γ^(-1)) u_(γδ)`. In the groupoid
algebra, `F = Ψ(f u_γ)` lives on the sheet `γ` and `G = Ψ(g u_δ)` on the sheet `δ`. So `F * G` lives on the
sheet `γδ`, with

```text
(F * G)(γδ, x) = F(γ, δx) G(δ, x) = f(γδx) g(δx).
```

`Ψ(f (g o γ^(-1)) u_(γδ))(γδ, x) = f(γδx) · g(γ^(-1) γδx) = f(γδx) g(δx)` gives the same value.
Both sides are bilinear, so `Ψ` is multiplicative. It is unital, since `Ψ(1 · u_e) = 1_(X)` is the unit.

**Effective and minimal.**
- Minimality of the groupoid is minimality of the action.
- A topologically free action gives an effective groupoid: the interior of the isotropy is the unit space.
- A minimal subshift without periodic points is free, so `X ⋊_T Z` is effective and minimal.

Credit: this identification is standard in the Steinberg-algebra literature. It is written out here because
the UN dictionary needs it at arbitrary coefficient rings, and no source with a verified theorem number was
read.
