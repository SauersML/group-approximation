---
rg: 2
id: spectrally-complete-tuples-bound-commutative-rank
kind: claim
title: A commutative subalgebra containing a spectrally complete commuting s-tuple has transcendence degree at most s; nondegenerate band elements of LC(X,K) ⋊ Z are spectrally complete, so no F[Z^2] there contains one
distinct_from:
  algebraic-core-gradings-bound-homogeneous-laurent-rank: that bounds the rank for homogeneous units (grading) and for locally matrix algebras; this bounds it for arbitrary, non-homogeneous commutative subalgebras that contain one spectrally complete tuple, via eigenspaces of an orbit representation.
  leavitt-commuting-units-are-algebraically-dependent: that asks for every pair of commuting units of L(1,2); this proves dependence only when one member of the tuple is spectrally complete.
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that asks whether F_2[Z^4] embeds; this kills every embedding whose image meets a spectrally complete tuple of the matching size.
---

**ESTABLISHED (unreviewed).** Let `K` be a field, `K̄` an algebraic closure, `Ξ` a set.
Let `A` be a `K`-algebra with a faithful representation `π` on the space `K^Ξ` of all
functions `Ξ → K`, by *row-finite* matrices. Row-finite means each row has finitely many
nonzero entries, as for the orbit representations of Steinberg algebras of ample groupoids.
Write `π` also for its extension to `A ⊗ K̄` acting on `K̄^Ξ`.

**Definition.** Let `L_1, …, L_s ∈ A` commute, and for `μ ∈ K̄^s` put
`W_μ = ⋂_i ker(π(L_i) − μ_i) ⊆ K̄^Ξ`. The tuple is *spectrally complete* if there are
- a Zariski-dense set `M ⊆ K̄^s`, an integer `d ≥ 1`, and
- functions `ψ_1, …, ψ_d : Ξ → K̄(μ_1, …, μ_s)` whose entries have no pole on `M`,

such that
- (SC1) for each `μ ∈ M` the specialisations `ψ_1(μ), …, ψ_d(μ)` form a basis of `W_μ`;
- (SC2) for every finite `F ⊆ Ξ`, the restrictions `ψ_j(μ)|_F` (`μ ∈ M`, `j ≤ d`) span `K̄^F`.

**Theorem B (spectral bound).** Let `(L_1, …, L_s)` be spectrally complete.
1. If `P ∈ A` commutes with every `L_i`, there is `Φ ∈ K̄[μ_1, …, μ_s, y]` of
   `y`-degree `d`, with leading coefficient `D(μ) ≠ 0`, such that `Φ(L, P) = 0`.
2. For every nonzero `g ∈ K̄[μ]`, `g(L)` is a non-zero-divisor on the commutant of the `L_i`.
3. A commutative subalgebra `C ⊆ A` containing `L_1, …, L_s` contains no polynomial ring
   `K[x_1, …, x_{s+1}]`. So it contains no `K[Z^{s+1}]` and no domain of transcendence degree `s + 1`.

**Theorem A (nondegenerate band elements).** Let `(X, T)` be an infinite minimal Cantor
system and `A = LC(X, K) ⋊_T Z`. Write `L = Σ_{k=p}^{q} a_k u^k` with `a_p, a_q ≠ 0`.
Call `L` *nondegenerate* if
- it is not in `LC(X, K)`, that is, `p < 0` or `q > 0`;
- `a_q` is a unit of `LC(X, K)` (nowhere zero) when `q > 0`;
- `a_p` is a unit when `p < 0`.

Then `(L)` is spectrally complete, with `d = max(q, 0) − min(p, 0)`, in every orbit
representation. So every element commuting with `L` is algebraic over `K[L]`, and no commutative
subalgebra containing `L` contains `K[x, y]`.

Over `F_2` a unit of `LC(X, F_2)` is `1`, so "nondegenerate" means that both extreme
coefficients on the far side of `0` equal `1`. Examples are `u + f`, `u^{-1} + f + u` and
`1 + f u + u^2` for any `f`.

**Corollary (Z^1 test of the commutative-rank conjecture).** If `F_2[Z^2] ↪ LC(X, F_2) ⋊ Z`,
then every nonscalar element of the image is degenerate: an extreme coefficient beyond
offset `0` vanishes somewhere. The same holds for any commutative subalgebra of
transcendence degree 2.

**Theorem C (directional tuples in Z^s crossed products).** Let `Z^s` act on a Cantor
space `Ω` with a dense free orbit `Z^s · ω`, and `A = LC(Ω, K) ⋊ Z^s`. Let `v_1, …, v_s ∈ Z^s`
be linearly independent. Let `L_i = Σ_{k=p_i}^{q_i} a_{i,k} u_{k v_i}` with `a_{i,k} ∈ LC(Ω, K)`,
each nondegenerate as in Theorem A: `p_i < 0` or `q_i > 0`, and the extreme coefficients on
the far side of `0` are units. If the `L_i` commute, then
`(L_1, …, L_s)` is spectrally complete, with `d = [Z^s : ⊕ Z v_i] · ∏ d_i`. So Theorem B applies.
For `s = 2` and `B_Ω`: an embedded `F_2[Z^3]` contains no commuting directional
nondegenerate pair.

**Scope and residual.** Theorem B applies to `B_Ω ⊗ L_∂` and to every Steinberg algebra, since
orbit representations are row-finite and jointly faithful. The class it does *not* reach is
the spectrally incomplete elements: degenerate band elements whose eigenspaces are zero or
infinite-dimensional. Examples are `1_U u` (nilpotent) and `u_g` for `g ∈ [[T]]` with
infinitely many orbits on one `T`-orbit. The residual `s = 1` question is recorded as
`minimal-cantor-z-crossed-products-contain-no-f2-z2`.
