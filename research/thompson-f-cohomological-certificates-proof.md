---
rg: 2
id: thompson-f-cohomological-certificates-proof
kind: route
title: The x_0-tail bump group is amenable, normalish and starts a commensurating chain to F, so BKKO, Gaboriau and Monod kill every cohomological, l2 and cost certificate outside Johnson's module
target: thompson-f-cohomology-certificates-cannot-prove-nonamenability
requires:
  - thompson-f-has-an-amenable-normalish-tail-subgroup
  - amenable-normalish-kills-l2-betti-bounded-cohomology
  - thompson-f-bounded-cohomology-vanishes-separable-duals
---

Let `T` and `T_(≥M)` be as in `thompson-f-has-an-amenable-normalish-tail-subgroup`. That claim gives: `T`
is amenable and normalish; every finite intersection of conjugates contains a tail `T_(≥M)`;
`x_0^(-1) T x_0 ⊇ T`; `x_1^(-1) T x_1 = T`.

## Item 1 (l2-Betti numbers)

`amenable-normalish-kills-l2-betti-bounded-cohomology`, item 1, applied to `T ≤ F`.

## Item 2 (fixed price 1)

Gaboriau, *Coût des relations d'équivalence et des groupes*, Invent. Math. 139 (2000), Critères VI.24(3).
The verbatim text was imported into this graph in `fpbs-elementary-matrix-semidirect-fixed-price-one-citation`:

> si Γ est une réunion croissante de groupes infinis Γ_n où Γ_1 est à prix fixe de coût 1, par exemple
> moyennable, et si Γ_{n+1} est engendré par Γ_n et des éléments γ ∈ Γ tels que γ^{-1}Γ_nγ ∩ Γ_n soit
> infini alors Γ est à prix fixe de coût 1.

The chain for `F`:
- `Γ_1 = T`, which is infinite and amenable.
- `Γ_2 = ⟨Γ_1, x_0⟩`, with `x_0^(-1) Γ_1 x_0 ∩ Γ_1 ⊇ T` infinite.
- `Γ_3 = ⟨Γ_2, x_1⟩`, with `x_1^(-1) Γ_2 x_1 ∩ Γ_2 ⊇ x_1^(-1) T x_1 ∩ T = T` infinite.
- `Γ_n = F` for `n ≥ 3`, because `F = ⟨x_0, x_1⟩`.

All `Γ_n` are infinite, so `F` has fixed price 1. The certificate class (b) needs the recalled theorem
that infinite amenable groups have fixed price 1 (Ornstein–Weiss, Levitt). Gaboriau's own text includes
it ("par exemple moyennable").

## Item 3 (separable coefficients)

This is `thompson-f-bounded-cohomology-vanishes-separable-duals`, Theorem 2.

## Item 4 (tail gate)

BKKO, arXiv:1410.2518, proof of Proposition `thm:trivial-bdd-cohomology`. It was read from the e-print TeX
source (`c-star-simple-oct19-2016.tex`, l.645–657) on 2026-09-17. Verbatim:

> "The proof of the next result is similar to the proofs of \cite{M2001}*{Corollary 7.5.9, Corollary 7.5.10}."

> "Let $H \le G$ be an amenable normalish subgroup. We can compute the bounded cohomology of $G$ using
> the complex $0 \longrightarrow \ell^\infty(G/H,E)^G \longrightarrow \ell^\infty((G/H)^2,E)^G
> \longrightarrow \ell^\infty((G/H)^3,E)^G \longrightarrow \cdots$ We claim that
> $\ell^\infty((G/H)^n,E)^G$ vanishes, and hence that $H_b^n(G,E)$ also vanishes. To see this, fix
> $f \in \ell^\infty((G/H)^n,E)^G$. Then for every $t = (t_1,\ldots,t_n) \in (G/H)^n$, the element
> $f(t) \in E$ is left invariant by every element in $\cap_i t_i H t_i^{-1}$."

The computation of `H_b^*` through this complex uses only that `H` is amenable (Monod, LNM 1758, Cor. 7.5.9
and 7.5.10, as cited there). Mixing is used only in the last sentence of that proof. Take `G = F`, `H = T`
and a dual module `E` with `E^(T_(≥M)) = 0` for every `M`. For `t = (t_1 T, …, t_n T)`, pick
representatives `t_i`. By the tail claim, `⋂_i t_i T t_i^(-1) ⊇ T_(≥M)` for some `M`, so
`f(t) ∈ E^(T_(≥M)) = 0`. The whole complex is zero, hence `H_b^n(F,E) = 0` for all `n ≥ 0`.

A mixing module is tail-mixing, since each `T_(≥M)` is infinite. `ℓ^p(F)` is mixing, as BKKO state
verbatim.

## Item 5 (C_reg, D_reg)

BKKO, same source, l.673 and l.679, verbatim:

> "The class of groups $\C_{\text{reg}}$ was introduced in \cite{MS2006}*{Notation 1.2}. It consists of
> those countable discrete groups $G$ satisfying $H_b^2(G,\ell^2(G)) \ne 0$ [...] This includes groups
> admitting a non-elementary proper isometric action on some Gromov-hyperbolic graph of bounded valency,
> groups admitting a non-elementary proper isometric action on some proper CAT(-1) space, and groups
> admitting a non-elementary simplicial action on some simplicial tree."

> "By \cite{T2009}*{Lemma 2.8}, every group in $\D_{\text{reg}}$ has either non-vanishing first
> $\ell^2$-Betti number or non-trivial second bounded cohomology with coefficients in $\ell^2(G)$."

`H_b^2(F, ℓ^2 F) = 0` by item 4 (or item 3), so `F ∉ C_reg`. `β_1^(2)(F) = 0` by item 1, so `F ∉ D_reg`.
The two proper actions in the quoted list would put `F` in `C_reg`. The tree clause of the quote lacks the
properness hypothesis of Monod–Shalom: `F_2 × Z` acts non-elementarily on the tree of `F_2`, yet
`H_b^2(F_2 × Z, ℓ^2) = 0` by BKKO. So the tree clause is not used.

## Calibration

`F_2 × Z` is non-amenable, and `1 × Z` is normal, infinite and amenable, hence normalish. Items 1 and 4
follow from BKKO. Item 2 follows from the chain `Z ⊂ ⟨Z, a⟩ ⊂ ⟨Z, a, b⟩`, where `a, b` commute with `Z`.
Item 5 follows as above. For item 3, the calibration is Monod's remark on piecewise-projective groups
(verbatim in the imported claim). ∎
