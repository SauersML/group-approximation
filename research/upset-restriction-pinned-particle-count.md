---
rg: 2
id: upset-restriction-pinned-particle-count
kind: route
title: Letters outside an upset never appear where they were not, so configurations with finitely many of them form compact invariant pieces, and a fibre count from the bijective restriction shows each piece is carried onto itself
target: strict-automaton-upsets-give-smaller-nonsurjunctive-sizes
requires: []
---

Complete proof. Notation as in the target. Call a site `g` a *particle* of `x` if `x(g) ∉ U`.

## Step 1. Particles are never created

If `x(g) ∈ U` then `τ(x)(g) ∈ U`, because `(x(g), τ(x)(g)) ∈ R(τ)` and `U` is an upset. So the particle set of
`τ(x)` is contained in that of `x`. For a finite `F ⊆ G` put

`D_F = {x ∈ A^G : x(g) ∈ U for all g ∉ F} ≅ A^F × U^(G \ F)`.

It is closed, and `τ(D_F) ⊆ D_F`.

## Step 2. The far output reads only the far input

Put `S = F M^(-1)`, finite. `S ⊇ F` since `1 ∈ M`. The output `τ(x)(g)` reads `x` on `gM`, and `gM ∩ F = ∅`
exactly when `g ∉ S`. So there is a map `Θ : U^(G \ F) -> U^(G \ S)` with `τ(x)|_(G \ S) = Θ(x|_(G \ F))` for
every `x ∈ D_F`. It takes values in `U` by Step 1.

## Step 3. Fibre sizes of `Θ`, from the bijective restriction

`τ_U` is injective (a restriction of `τ`) and onto by hypothesis, so it is a bijection of `U^G`. Fix
`t ∈ U^(G \ S)`. The set `W_t = {w ∈ U^G : w|_(G \ S) = t}` has `|U|^|S|` elements, so its preimage under `τ_U`
has `|U|^|S|` elements. By Step 2 (with `F`-coordinates in `U`) that preimage is

`{u ∈ U^G : Θ(u|_(G \ F)) = t} = U^F × Θ^(-1)(t)`.

Hence `|Θ^(-1)(t)| = |U|^(|S| - |F|) = |U|^|S \ F|`. In particular it is finite.

## Step 4. `τ` carries `D_F` onto itself

Fix `y ∈ D_F` and put `t = y|_(G \ S) ∈ U^(G \ S)`. Let

- `P_t = {x ∈ D_F : Θ(x|_(G \ F)) = t} = A^F × Θ^(-1)(t)`, of size `|A|^|F| |U|^|S \ F|` by Step 3;
- `Z_t = {z ∈ D_F : z|_(G \ S) = t}`, which is `A` on `F`, `U` on `S \ F`, and `t` elsewhere, of the same size
  `|A|^|F| |U|^|S \ F|`.

By Steps 1 and 2, `τ(P_t) ⊆ Z_t`. `τ` is injective, so `τ : P_t -> Z_t` is an injection between finite sets of the
same size, hence onto. Since `y ∈ Z_t`, `y ∈ τ(D_F)`.

## Step 5. Surjectivity

`U ≠ ∅`, so `⋃_F D_F` is dense in `A^G`: a cylinder fixed on a finite `F` meets `D_F` (fill the rest with a
letter of `U`). By Step 4 `τ(A^G)` contains this dense set. `τ(A^G)` is compact, hence closed, so it is `A^G`. ∎

## Corollaries

1. If `τ` is strict, `τ_U` is injective and, by the theorem, not onto. It is a cellular automaton over `U` with
   memory `M` and table `μ|_(U^M)`, so `|U| ∈ NS(G)`.
2. `τ^p` is injective, and not onto (else `τ` is onto). The pair `(x(g), τ^p(x)(g))` is joined by the path
   `x(g) -> τ(x)(g) -> ... -> τ^p(x)(g)` in `R(τ)`, so `R(τ^p) ⊆ R(τ)^p`. A set closed under `R(τ)^p` is an upset of
   `τ^p`; apply corollary 1 to `τ^p`. A sink class `C` of period `d` has cyclic classes `V_0, ..., V_(d-1)` with every
   arc from `V_i` landing in `V_(i+1 mod d)` (arcs leaving `C` do not exist), so each `V_i` is closed under `R(τ)^d`.
3. At `k = n0 = min NS(G)` no proper nonempty upset of any `τ^p` exists, since its size would be a smaller element of
   `NS(G)`. A digraph with no proper nonempty forward-closed set is strongly connected. If `R(τ)` had period
   `d > 1`, its cyclic classes would be proper upsets of `τ^d` by corollary 2. So `R(τ)` is primitive.
4. A capacity `n` has `n(a) <= n(b)` along arcs, and around a strongly connected digraph this forces `n` constant.
5. Given in the target.

## Sharpness

The hypothesis that `U` is closed *sitewise* cannot be weakened to `τ(U^G) ⊆ U^G`. An injective `τ` maps each
constant `a^G` to a constant, and so permutes the constants by some `σ`. Then `ρ = τ^(ord σ)` is strict whenever `τ`
is, and fixes every `a^G`. `{a}` is `ρ`-invariant on configurations, and `ρ_{a}` is onto, while `ρ` is not.
