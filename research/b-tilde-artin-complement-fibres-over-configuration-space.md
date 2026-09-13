---
rg: 2
id: b-tilde-artin-complement-fibres-over-configuration-space
kind: claim
title: A finite cover of the B̃_n orbit space embeds in a space fibring over a configuration space of C^× with punctured-surface fibres
distinct_from:
  c-tilde-artin-groups-are-punctured-plane-braid-groups: that imports Allcock's realization of A(C̃_n) as a braid group of the twice-punctured plane; this imports the Li--Roushon fibration for the B̃_n arrangement complement, whose fibres are punctured surfaces of growing genus, not configuration spaces.
  artin-groups-satisfy-boone-higman: that is the open problem over all Artin groups; this is a topological input about one Euclidean type and says nothing about simple groups.
artifacts:
  - research/artifacts/bh-b-tilde-artin-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `n >= 3`. Let `A(B̃_n)` and
`W = W(B̃_n)` be the Euclidean Artin group and the affine Weyl group of type
B̃_n.

1. **The orbit space.** Let
   `M = {u ∈ C^n | u_i ± u_j ∉ Z for i ≠ j; u_k ∉ Z}`. Then `W` acts properly
   discontinuously on `M`, and `A(B̃_n) ≅ π_1(M/W)`.
2. **Three changes of space.**
   - `u ↦ e^(2πiu)` induces a covering
     `M → N = {v ∈ C^n | v_i ≠ v_j^(±1) for i ≠ j; v_k ≠ 0, 1}`.
   - `α ↦ (α+1)/(α−1)` induces a homeomorphism
     `N → P = {w ∈ C^n | w_i ≠ ±w_j for i ≠ j; w_k ≠ ±1}`.
   - `(w, λ) ↦ (λ, λw_1, …, λw_n)` is a homeomorphism `P × C^× → Y_(n+1)`.
3. **The fibration.** For `m >= 3` let
   - `Y_m = {y ∈ C^m | y_i ≠ ±y_j for i ≠ j; y_1 ≠ 0}`,
   - `Z_m = {z ∈ (C^×)^(m−1) | z_i ≠ z_j for i ≠ j}`.

   Then `f(y) = (y_1(y_1² − y_m²), …, y_1(y_(m−1)² − y_m²))` is a locally
   trivial fibration `Y_m → Z_m`. Its fibres are connected surfaces of genus
   `(3m−6)·2^(m−3) + 1` with `3·2^(m−2)` punctures, and
   `1 → π_1(f^−1(z)) → π_1(Y_m) → π_1(Z_m) → 1` is exact.

## Source

L. Li and S. K. Roushon, *The affine Artin group of type B̃_n is virtually
poly-free*, arXiv:2403.09533v2 (24 Oct 2025). Journal ref, from the abs page:
Bull. Sci. Math. 206 (2026) 103760. Read from the LaTeX source on 2026-09-12;
LaTeX is rendered as text below.

- **Item 1**, proof of Theorem `mt`: "Recall that W_{B̃_n} acts properly
  discontinuously on M_{B̃_n} and A_{B̃_n} ≃ π_1(M_{B̃_n}/W_{B̃_n})". The
  paper cites Nguyễn (Topology 22 (1983), Section 5) for the exact sequence
  that follows, and Allcock (Trans. Amer. Math. Soc. 354 (2002), Section 4)
  for `M`. Neither is re-read here.
- **Item 2**, same proof: the covering `M → N` induced by "exp", the
  homeomorphism `N → P` induced by `η(α) = (α+1)/(α−1)`, and the homeomorphism
  `P × C^* → {y ∈ C^(n+1) | y_i ≠ ±y_j, for i ≠ j; y_1 ≠ 0}`,
  `(w_1, …, w_n, λ) ↦ (λ, λw_1, …, λw_n)`. All three are displayed there.
- **Item 3**, Proposition `fibration`, stated with `n` where this node writes
  `m`: "is a locally trivial fibration, with non-compact connected fibers
  homeomorphic to a 2-manifold of genus (3n−6)2^{n−3}+1, with 3·2^{n−2} points
  removed". The short exact sequence is displayed in its proof, after "using
  the fact that Z is aspherical".
- The Remark after the Proposition: the referee pointed out that it "is also a
  special case of the main result in [ADR20]", which is Amend--Deligne--Röhrle,
  Compos. Math. 156 (2020) 526--532. Not read.

## What was checked (not a new proof)

These are recorded in `research/artifacts/bh-b-tilde-artin-2026-09-12.md` §4.

1. **The type.**
   - The chamber `u_1 > … > u_n > 0`, `u_1 + u_2 < 1` has walls with normals
     `e_1 + e_2`, `e_i − e_(i+1)` and `e_n`.
   - They give a branch at one end of the diagram and a double edge at the
     other, so the type is B̃_n. The C̃_n arrangement uses `u_k ∈ ½Z` instead.
2. **W acts freely on M.** A fixed point would lie on a complexified
   hyperplane, by Steinberg's theorem on the stabilizer.
3. **The fibres lie in Y_m.** A solution of `f(y) = z` with `y_1 ≠ 0`
   automatically satisfies `y_i ≠ ±y_j`.
4. **Genus and punctures.**
   - Riemann--Hurwitz for `y ↦ y_1`, of degree `2^(m−1)`, re-done.
   - Independently, a finite-field point count gives the Poincaré polynomial
     `(1+t)(1+3t)⋯(1+(2m−3)t)(1+mt)` of `Y_m`.
   - Multiplicativity over `{z_1 = 1} ≅ Conf_(m−2)(C − {0,1})` then gives
     `χ(fibre) = −3(m−1)·2^(m−2)`.
   - That agrees with `2 − 2g − p`.

**Not reproved:**
- local triviality, i.e. Thom's first isotopy lemma with the Jacobian-rank
  Lemmas `submersion` and `smooth`;
- connectedness of the fibre;
- Nguyễn's identification in item 1.
