---
rg: 2
id: thompson-f-amenable-iff-dyadic-action-extensively-amenable-proof
kind: route
title: Embed F in the integer lamplighter over the dyadics by its breakpoint cocycle and apply the JMBMdlS subgroup criterion
target: thompson-f-amenable-iff-dyadic-action-extensively-amenable
requires: [affine-lamplighter-amenable-iff-extensively-amenable]
---

**Source.** K. Juschenko, N. Matte Bon, N. Monod, M. de la Salle, *Extensive amenability and an
application to interval exchanges*, arXiv:1503.04977 (ETDS 38 (2018) 195–219). The arXiv source
`extAmen2.tex` was fetched and read on 2026-09-17.

**Verbatim 1 (functors, §1).** "Denote by $\cati$ the category of finite sets whose morphisms are injective
maps. Denote further by $\cata$ the category of amenable groups with group homomorphisms. Since $\cata$ has
direct limits, any functor $F\colon\cati\to\cata$ extends to the category of all sets with injective maps as
morphisms by setting $F(X)$ to be the direct limit of $F(Y)$ as $Y$ runs over the directed set $\Pf(X)$."

**Verbatim 2 (Example "ex:wreath", §3).** "Fix an amenable group $A$. Consider the functor $F$ which maps
any finite set $Y$ to $A^Y$ with the obvious extension map on inclusions. Then for a general set $X$ we have
$F(X)=A^{(X)}$, the restricted product."

**Verbatim 3 (Corollary "prop:functor:amenable:intro", §1).** "Let $G \acts X$ be an extensively amenable
action and let $F\colon \cati \to \cata$ be any functor. A subgroup $H$ of $F(X) \rtimes G$ is amenable as
soon as the intersection $H \cap (\{1\} \times G)$ is so."

**Verbatim 4 (Remark "R: method", §1).** "A particular case in which this criterion applies is when one is
able to construct a \emph{twisted embedding} $G\hookrightarrow F(X)\ltimes G$ of the form $g\mapsto (c_g,
g)$ with the property that $\{g\in G\: : \: c_g=1\}$ is an amenable subgroup of $G$. [...] The conclusion is
then that $G$ is amenable."

**Verbatim 5 (Proposition "P: extension", §2).** "Let $G$ be a group acting on two sets $X,Y$ and let
$q\colon X \to Y$ be a $G$-map. If $G \acts Y$ is extensively amenable and if $G_y \acts q^{-1}(y)$ is
extensively amenable for every $y \in Y$, then $G \acts X$ is extensively amenable. The converse holds if
$q$ is surjective."

The forward direction "amenable group implies extensively amenable action" is JMBMdlS Lemma 2.1, already
imported verbatim in `affine-lamplighter-amenable-iff-extensively-amenable` (the required claim).

## Step 1. The breakpoint cocycle

Let `P` be the group of orientation-preserving homeomorphisms of `[0,1]` that are piecewise linear with
finitely many breakpoints. For `f ∈ P` and `x ∈ (0,1)` put `β(f)(x) = log₂ f'(x⁺) − log₂ f'(x⁻)`. This is a
finitely supported real function on `(0,1)`, and `β(f) = 0` exactly when `f` is linear, i.e. `f = id`. Let
`P` act on functions by `(k·φ)(x) = φ(k⁻¹x)`.

The chain rule `(fh)'(x^±) = f'(h(x)^±)·h'(x^±)` gives `β(fh)(x) = β(f)(h(x)) + β(h)(x)`, that is

  (R)  `β(fh) = h⁻¹·β(f) + β(h)`.

For `g ∈ F` the breakpoints lie in `D` and the slopes are powers of `2`, so `β(g) ∈ Z^{(D)}`, and `F`
preserves `D`. Put `c_g = β(g⁻¹)`. By (R), `c_{gh} = β(h⁻¹g⁻¹) = g·β(h⁻¹) + β(g⁻¹) = c_g + g·c_h`.

In `Z^{(D)} ⋊ F` with law `(a,g)(b,h) = (a + g·b, gh)` this says `(c_g,g)(c_h,h) = (c_{gh}, gh)`. So
`ι(g) = (c_g, g)` is a homomorphism, injective because its second coordinate is `g`.

## Step 2. Trivial kernel

`H = ι(F)` is a subgroup of `Z^{(D)} ⋊ F`, and `H ∩ ({0} × F) = {(c_g, g) : c_g = 0}`. If `c_g = 0` then
`g⁻¹ ∈ F` has no breakpoint in `(0,1)`, so `g⁻¹` is linear and fixes `0` and `1`, so `g = id`. The
intersection is trivial, hence amenable.

## Step 3. Item 1

(⇒) Lemma 2.1 (Verbatim in the required claim).

(⇐) Suppose `F ↷ D` is extensively amenable. `Z` is amenable, so by Verbatims 1–2 `Y ↦ Z^Y` is a functor
`I → Amen` with `F(D) = Z^{(D)}`. The `F`-action on `Z^{(D)}` defining the semidirect product is induced by
functoriality from the permutation of `D`, i.e. `(g·φ)(x) = φ(g⁻¹x)`, the action used in Step 1. By
Verbatim 3 applied to `G = F`, `X = D` and the subgroup `H` of Step 2, `H` is amenable. Since `H ≅ F`, `F`
is amenable. This is exactly the method of Verbatim 4 with an amenable (trivial) kernel.

## Step 4. Item 2

Let `X` be a transitive `F`-set and `q : X → D` an `F`-map. `D` is one `F`-orbit
(`f-dyadic-ea-iff-inverted-orbit-confinement-proof`, transitivity check), so `q` is surjective. If
`F ↷ X` is extensively amenable, the converse part of Verbatim 5 gives that `F ↷ D` is extensively amenable,
so `F` is amenable by Step 3. Conversely, if `F` is amenable, Lemma 2.1 gives extensive amenability of
`F ↷ X`.

An `F`-map `F/H → D` exists iff `H ≤ F_y` for some `y ∈ D` (send `gH ↦ g(y)`). This holds for `H = {1}`, for
the stabilizer of a finite set `{y_1 < … < y_k} ⊂ D` (elements of `F` preserve order, so they fix `y_1`), and
for `F_{[0,a]}`, `F_{[a,1]}` with `a ∈ D` (they fix `a`).

## Step 5. The affine action is free

Here `g ∗ φ = c_g + g·φ` on `Z^{(D)}`. It is the action of `ι(F)` on `Z^{(D)} = (Z^{(D)} ⋊ F)/F`, so it
is an action. Suppose `g ∗ φ = φ`. Choose `ψ ∈ P` with breakpoint set `supp φ` and jumps `β(ψ) = φ`: take
slopes `λ·2^{s_i}` on the successive pieces, with `s_i` the partial sums of `φ` and `λ > 0` normalizing the
total length to `1`. By (R), `β(ψg⁻¹) = g·β(ψ) + β(g⁻¹) = g ∗ φ = φ = β(ψ)`. By (R) again,
`β(ψ⁻¹) = −ψ·β(ψ)` and `β(ψg⁻¹ψ⁻¹) = ψ·β(ψg⁻¹) + β(ψ⁻¹) = ψ·φ − ψ·φ = 0`. So `ψg⁻¹ψ⁻¹ = id` and
`g = id`. Step 5 is used only in `thompson-f-dyadic-ea-witnesses-need-tower-size-proof`.
