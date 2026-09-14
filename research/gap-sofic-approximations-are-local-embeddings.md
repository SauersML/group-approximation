---
rg: 2
id: gap-sofic-approximations-are-local-embeddings
kind: claim
title: A group is LEF iff it has sofic approximations inside permutation groups with a uniform fixed-point gap
distinct_from:
  kazhdan-ergodic-sofic-centralizer-forces-lef: that derives LEF from property (T) and an ergodic centralizer of one sofic embedding; this derives LEF from a uniform gap in the fixed-point ratios of the target permutation groups, with no hypothesis on the group.
  lef-simple-rings-are-not-finitely-presented: that is the ring statement that an infinite simple LEF ring has no finite presentation; this is the group statement that sofic approximations through gap targets, such as linear, affine or projective linear maps, are local embeddings.
  sofic-fp-simple-kazhdan-group-from-fp-simple-ring: that is the ring-route existence question; this proves that its soficity gate (c) cannot be met through linear, affine or projective linear models over finite fields.
---

**ESTABLISHED (reviewed: sk-verify-3 PASS, sk-verify-26 PASS).**

**Definitions.**
- For a finite set `Ω` and `a, b ∈ Sym(Ω)`, `d(a, b) = |{ω : aω ≠ bω}| / |Ω|`. The fixed-point
  ratio is `fpr(x) = |Fix(x)| / |Ω| = 1 - d(x, 1)`.
- A *sofic approximation* of a countable group `G` is a sequence of maps `σ_N : G -> Sym(Ω_N)` with
  `d(σ_N(gh), σ_N(g) σ_N(h)) -> 0` for all `g, h` and `d(σ_N(g), 1) -> 1` for `g ≠ e`.
- Subgroups `H_N ≤ Sym(Ω_N)` have a *fixed-point gap* `δ > 0` if `fpr(x) ≤ 1 - δ` for every
  `x ∈ H_N \ {1}`. Equivalently, distinct elements of `H_N` differ on a proportion at least `δ` of
  the points.

**Theorem.** A countable group `G` is LEF iff it has a sofic approximation with `σ_N(G) ⊆ H_N` for
subgroups `H_N` with a common fixed-point gap.

**Gap families (proved in the route).**
- (A) Affine maps `y ↦ a α(y)` of a finite group `A` (`a ∈ A`, `α ∈ Aut(A)`) acting on `A`: gap
  `1/2`. This covers `GL_m(F_q)` and `AGL_m(F_q)` on `F_q^m`, and `Aut(A)` on `A`.
- (P) `PGL_m(F_q)` on the projective space `P^(m-1)(F_q)`, `m >= 2`: gap `1/2`.
- Not used: fixed-point-ratio bounds for primitive actions of groups of Lie type (Liebeck--Saxl),
  which were not read at source.

**Corollaries.**
1. A finitely presented group with a gap sofic approximation is residually finite.
2. Let `S` be finitely presented, infinite and simple, with relators of length at most `L`. For every
   sofic approximation of `S` and all large `N`, some defect `σ_N(gh)^(-1) σ_N(g) σ_N(h)` with
   `g, h` in the ball of radius `L` is a nontrivial permutation, and its fixed-point ratio tends to
   `1`. So `S` has no sofic approximation through linear, affine or projective linear maps of finite
   vector spaces, or through automorphisms of finite groups acting on themselves.
3. Ring route (`sofic-fp-simple-kazhdan-group-from-fp-simple-ring`). If `S = EL_n(R)/Z` is finitely
   presented, infinite and simple, no sofic approximation of `S` takes values in `F_q`-linear maps
   acting on vectors or in projective linear maps acting on lines. The remark recorded there, that a
   rank defect `r` becomes a Hamming defect `1 - q^(-O(r))`, is the quantitative form of this
   exactness.
4. For `G_X = EL_3(LC(X, F_2) ⋊ Z)`, sofic models by elements of `GL_(3N)(F_2)` acting on `F_2^(3N)`
   are automatically local embeddings. So LEF is the whole content such models can carry, and a
   finitely presented analogue needs models of a different kind.

**Model test.**
- `Z` is LEF, and its regular models `Z/N` have gap `1`. The theorem holds.
- `Sym(Ω_N)` has no gap, since a transposition has `fpr = 1 - 2/|Ω_N|`. So the hypothesis is not
  automatic. The Baumslag--Solitar group `BS(2,3)` is finitely presented, sofic (residually solvable)
  and not residually finite, hence not LEF. Corollary 1 says each of its sofic approximations uses
  targets without a gap, which is consistent.
- Thompson's `V` is finitely presented, infinite and simple. Corollary 2 excludes gap models for it,
  consistent with its open soficity.

**Credit.** This is the standard observation that algebraic finite models have large minimum Hamming
distance, combined with the standard fact that finitely presented LEF groups are residually finite
(Vershik--Gordon 1997). No novelty is claimed. Bounded search: a grep of this graph for
fixed-point-ratio and exact-model statements on 2026-09-13, and no literature search for this form.

Route: `gap-sofic-approximations-are-local-embeddings-proof`.

**Review (sk-verify-3, 2026-09-13): PASS.** Both directions, the affine and projective gap bounds, and Corollaries 1–4 re-derived; model tests consistent. No change needed. Credit note (recalled): an instance of the folklore fact that approximation through uniformly discrete bi-invariant metrics is LEF. See `research/artifacts/sk-review-3-2026-09-13-part2.md`.

**Review (sk-verify-26, 2026-09-14): PASS, second independent review.** All re-derived by hand:
- both directions, including injectivity from `d(σ(g),σ(h)) ≥ d(σ(h⁻¹g),1) − o(1)`, which needs only a distance bounded away from 0;
- gap (A): the fixed set is a coset of `A^α`, and the maps are the faithful holomorph;
- gap (P): the eigenspace count is an equality, merging leaves the smallest part `t`, and `f(m−t)+f(t)` is convex;
- Corollaries 1–2 by prefix induction on `B(r)` and `B(L)`.

Brute force on MSI: holomorph max fpr ≤ 1/2 for `Z/2, Z/3, Z/4, Z/5, Z/2×Z/2, Z/2×Z/4, S_3`, and `PGL_m(F_p)` max fpr equals the route's bound (1/3, 1/2, 1/3, 3/7, 5/13 for (m,p) = (2,2),(2,3),(2,5),(3,2),(3,3)). No literature import; the credit to Vershik–Gordon was not re-read at source. Status line fixed (it said unreviewed despite sk-verify-3). See `research/artifacts/sk-verify-26-2026-09-14.md`.
