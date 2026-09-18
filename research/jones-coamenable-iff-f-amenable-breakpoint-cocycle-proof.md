---
rg: 2
id: jones-coamenable-iff-f-amenable-breakpoint-cocycle-proof
kind: route
title: Co-amenability gives extensive amenability, and the functor corollary on the breakpoint cocycle gives amenability
target: jones-subgroup-coamenable-iff-thompson-f-amenable
requires: [dyadic-extensive-amenability-if-jones-subgroup-coamenable]
---

**Source imported.** K. Juschenko, N. Matte Bon, N. Monod and M. de la Salle, *Extensive amenability and an
application to interval exchanges*, arXiv:1503.04977, Ergodic Theory Dynam. Systems 38 (2018) 195–219. The
arXiv e-print (LaTeX source `extAmen2.tex`) was downloaded and read on 2026-09-17. The journal version was
not compared.

Verbatim (introduction, before Theorem 1.3): "Denote by $\cati$ the category of finite sets whose morphisms
are injective maps. Denote further by $\cata$ the category of amenable groups with group homomorphisms.
Since $\cata$ has direct limits, any functor $F\colon\cati\to\cata$ extends to the category of all sets with
injective maps as morphisms by setting $F(X)$ to be the direct limit of $F(Y)$ as $Y$ runs over the directed
set $\Pf(X)$." and "the reader can already have in mind $F(X) = A^{(X)}$ for an amenable group $A$".

Verbatim (Corollary 1.4, label `prop:functor:amenable:intro`): "Let $G \acts X$ be an extensively amenable
action and let $F\colon \cati \to \cata$ be any functor. A subgroup $H$ of $F(X) \rtimes G$ is amenable as
soon as the intersection $H \cap (\{1\} \times G)$ is so."

**(⇐) Amenable implies co-amenable.** If `m` is a left-invariant mean on `F`, its pushforward along
`g ↦ g\vec F` is an `F`-invariant mean on `F/\vec F`.

**(⇒) Co-amenable implies amenable.**
1. By `dyadic-extensive-amenability-if-jones-subgroup-coamenable`, `F ↷ D` is extensively amenable.
2. **Functor.** Take `A = ℤ`, i.e. the functor `Y ↦ ℤ^(Y)` with extension by zero along injections. Its
   extension to `D` is `ℤ^(D)`, with `F` acting by `(g·f)(x) = f(g⁻¹x)`, and
   `ℤ^(D) ⋊ F` has product `(a, g)(b, h) = (a + g·b, gh)`.
3. **Breakpoint cocycle.** For `g ∈ F` and `x ∈ D` let `β(g)(x) = log₂ g'(x⁺) − log₂ g'(x⁻)`. It is nonzero
   only at the finitely many breakpoints, which are dyadic, so `β(g) ∈ ℤ^(D)`. Each `h ∈ F` is increasing, so
   the chain rule on one-sided derivatives gives `β(gh)(x) = β(g)(hx) + β(h)(x)`. Put `c(g) = β(g⁻¹)`. Then
   `c(gh)(x) = β(h⁻¹)(g⁻¹x) + β(g⁻¹)(x) = (g·c(h))(x) + c(g)(x)`, so `g ↦ (c(g), g)` is a homomorphism
   `F → ℤ^(D) ⋊ F`. Its image `H` is a subgroup isomorphic to `F`.
4. **Trivial intersection.** If `(c(g), g) ∈ {0} × F`, then `g⁻¹` has no change of slope at any dyadic point.
   All breakpoints of elements of `F` lie in `D`, so `g⁻¹` is affine on `[0,1]` and fixes `0` and `1`, hence
   `g = 1`. So `H ∩ ({0} × F)` is trivial, in particular amenable.
5. By Corollary 1.4, `H ≅ F` is amenable. ∎
