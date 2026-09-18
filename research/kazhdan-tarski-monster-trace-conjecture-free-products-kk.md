---
rg: 2
id: kazhdan-tarski-monster-trace-conjecture-free-products-kk
kind: claim
title: The torsion-free trace-conjecture locus of marked groups is a G_delta closed under fast limits, so torsion-free Kazhdan Tarski monsters Q satisfy tau_*(K_0) in Z and Q * H has only trivial projections for every torsion-free hyperbolic H
distinct_from:
  kazhdan-torsion-free-tarski-monster-satisfies-kk: that proves only that C*_r(Q) itself has no nontrivial projection, and leaves the matrix form as an unestablished remark; this proves integrality of every K_0 trace of the interleaved monster, which is what free products need.
  kk-witness-counterexample-locus-is-marked-closed: that treats scalar witnesses and the Kadison--Kaplansky locus; this treats matrix witnesses with a non-integer trace window and the locus of the trace conjecture tau_*(K_0) in Z.
  free-product-kk-iff-trace-conjecture-for-factors: that is the per-group equivalence for free products; this supplies new factors satisfying its hypothesis.
  lueck-surjective-assembly-traces-lie-in-lambda-g: that gives integer K_0 traces under surjective assembly; this transfers integrality to direct limits where assembly is not known.
---

**ESTABLISHED** by `kazhdan-tarski-monster-trace-conjecture-free-products-kk-proof`, with the same
imports from Olshanskii--Osin--Sapir, *Lacunary hyperbolic groups*, Geom. Topol. 13 (2009) as
`kazhdan-torsion-free-tarski-monster-satisfies-kk-proof`.

Notation as in `kk-witness-counterexample-locus-is-marked-closed`: `F = F_d`, `M_d` the compact
space of normal subgroups `N ⊴ F`, `G_N = F/N`, `λ_N` the regular representation, `τ_N` the
canonical trace. For a matrix `x ∈ M_n(C[F])` write `Tr_N(x) = Σ_i τ_N(x_ii)`.

A **matrix witness** is `ω = (n, a, c, ε, δ)` with `n ≥ 1`, `a = a*` in `M_n(Q[i][F])`, and
rationals `c`, `ε > 0`, `0 < δ ≤ 1/2`. Put

```text
P_ω = { N ∈ M_d : spec λ_N(a) ∩ (c-ε, c+ε) = ∅  and  dist( Tr_N χ_(-∞,c)(λ_N(a)), Z ) ≥ δ }.
```

For `n = 1` this is the scalar witness set of `kk-witness-counterexample-locus-is-marked-closed`.

**Theorem M (the trace-conjecture locus).**
1. Every `P_ω` is closed in `M_d` and a `Π^0_1` class in `2^F`.
2. `τ_*(K_0(C*_r G_N)) ⊆ Z` iff `N ∉ ∪_ω P_ω`. So the **TR locus**, the marked groups whose
   reduced algebra has only integer `K_0` traces, is a `G_δ` in `M_d`.
3. **Radius.** If `G_N` is in the TR locus, then for every `ω` there is `r = r(N, ω)` such that
   every marked group agreeing with `G_N` on words of length `≤ r` lies outside `P_ω`.
4. **Fast limits.** Let `G(0) → G(1) → ...` be epimorphisms of `d`-marked groups in the TR locus,
   and enumerate the matrix witnesses `ω_1, ω_2, ...`. If the injectivity radius `r_i` of
   `G(i-1) → G(i)` satisfies `r_i ≥ r_{i-1}` and `r_i ≥ max_{k ≤ i} r(N_{i-1}, ω_k)`, then the
   direct limit is in the TR locus.

**Theorem T (monsters).** Let `G` be a torsion-free non-cyclic hyperbolic group with finite
generating set `S`. Then `G` has a quotient `Q` such that
1. `Q` is an infinite torsion-free Tarski monster (every proper subgroup cyclic), a direct limit of
   torsion-free hyperbolic groups with a graded small cancellation presentation;
2. **`τ_*(K_0(C*_r Q)) ⊆ Z`**; in particular `C*_r(Q)` has no projection other than `0, 1`.

**Corollary (free products).** Let `Q` be as in Theorem T and let `H` be a nontrivial torsion-free
group with `τ_*(K_0(C*_r H)) ⊆ Z`, for instance `Z`, any torsion-free hyperbolic group, or another
such monster. Then `C*_r(Q * H)` has no projection other than `0` and `1`.

When `G` is a torsion-free cocompact lattice in `Sp(n,1)`, `n ≥ 2`, the group `Γ = Q * Z` is
- torsion-free, finitely generated, not Kazhdan (it maps onto `Z`);
- not a-T-menable, since it contains the infinite Kazhdan group `Q`;
- not hyperbolic and not linear, since its subgroup `Q` is neither virtually cyclic nor contains
  `F_2` (Tits alternative for subgroups of hyperbolic and of linear groups);
- acylindrically hyperbolic, so for `Γ` Kadison--Kaplansky and the trace conjecture coincide
  (Corollary B of `fractional-matrix-trace-gives-projection-in-g-star-z`).

Neither Kadison--Kaplansky for `Q` alone nor any known assembly theorem gives the conclusion for
`Q * Z`. Corollary 3 of `free-product-kk-iff-trace-conjecture-for-factors` records that
Kadison--Kaplansky is not known to pass to free products without integer `K_0` traces on the
factors.

**Not claimed.** Baum--Connes for `Q` or `Q * H`. Integer traces for *every* torsion-free lacunary
hyperbolic group: the radius `r(N, ω)` has no uniform bound in terms of the hyperbolicity constant.
