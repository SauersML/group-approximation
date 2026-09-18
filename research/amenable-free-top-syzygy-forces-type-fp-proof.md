---
rg: 2
id: amenable-free-top-syzygy-forces-type-fp-proof
kind: route
title: The top L2-homology is the kernel of the last boundary map on a free module; a zero-dimensional submodule of a free U-module is zero, so a free top syzygy injects into a finitely generated free U-module and is bounded in rank
target: amenable-free-top-syzygy-forces-type-fp
requires:
  - amenable-fp-iff-affiliated-top-homology-vanishes
---

Notation and imports (J1)–(J3), (J6) are those of `amenable-fp-iff-affiliated-top-homology-vanishes-proof`.
`U = U(G)`. Tensor products are over `Z[G]`.

## Lemma 1 (zero-dimensional submodules of free modules)

Let `S` be any set and `M ⊆ U^(S)` a submodule with `dim_U M = 0`. Then `M = 0`.

*Proof.* Let `0 ≠ x ∈ M`. Then `x ∈ U^(S_0)` for a finite `S_0 ⊆ S`. `Ux` is a finitely generated
submodule of the finitely generated free module `U^(S_0)`, hence a direct summand by (J2), hence
finitely generated projective and nonzero. By (J1) `dim_U(Ux) > 0`. Monotonicity (J1) gives
`dim_U M >= dim_U(Ux) > 0`. ∎

## Lemma 2 (vanishing top homology)

If `G` is infinite and amenable, then `dim_U H_q(G; U) = 0` for all `q >= 1`.

*Proof.* (J3), transported from `NG` to `U` by flatness of `U` over `NG` and
`dim_U(U ⊗_NG M) = dim_NG(M)` (J1). ∎

In general `dim_U H_n(G; U) = b_n^(2)(G)`. Item 1 only needs this number to be `0`.

## Item 1

Let `0 → P → F_{n-1} → … → F_0 → Z → 0` be as in the target, `∂: P → F_{n-1}` the inclusion. It is a
projective resolution, so `H_n(G; U)` is the `n`-th homology of `U ⊗ P → U ⊗ F_{n-1} → …`. Since
there is nothing in degree `n+1`, `H_n(G; U) = ker(1 ⊗ ∂: U ⊗ P → U ⊗ F_{n-1})`.

Let `F ≤ P` be a free direct summand with basis `S`, so `U ⊗ F ≅ U^(S)` is a direct summand of
`U ⊗ P`. Then `ker((1 ⊗ ∂)|_{U ⊗ F}) ⊆ H_n(G; U)` has dimension 0 and lies in `U^(S)`, so it is zero
by Lemma 1. Hence `U^(S)` embeds in `U ⊗ F_{n-1} ≅ U^r`, with `r = rank F_{n-1}`. For every finite
`S_0 ⊆ S`, monotonicity gives `|S_0| = dim_U U^(S_0) <= r`. So `|S| <= r`.

If `P` is itself free, it is finitely generated free, and the resolution is finite free: `G` is of
type `FL`. ∎

## Item 2

Let `X` be an `n`-dimensional `K(G,1)` with finite `(n-1)`-skeleton. The cellular chain complex
of the universal cover `X̃` is a resolution of `Z` by free `Z[G]`-modules. `C_0, …, C_{n-1}` are
finitely generated. `∂_n: C_n → C_{n-1}` is injective, since `H_n(X̃) = 0` and there are no
`(n+1)`-cells. So `C_n` is a free top syzygy, and item 1 bounds the number of `G`-orbits of
`n`-cells, which is the number of `n`-cells of `X`, by `rank C_{n-1}`. ∎

## Item 3

Let `G` be finitely generated, amenable, with `cd G = 2`, and not `BS(1,m)`. `G` is infinite and
torsion-free. By item 4 of `amenable-fp-iff-affiliated-top-homology-vanishes`, `G` is not of type
`FP_2` and `H_1(G; U) ≠ 0`.

`0 → P → Z[G]^d → Z[G] → Z → 0` is exact with `P` projective by (J6), since `cd G = 2`.

(a) Let `F ≤ P` be a free direct summand of rank `k`. By item 1, `k <= d`. Put
`K = ker(U^d → U)`. The map `U^d → U` is onto because `H_0(G; U) = 0` for infinite finitely
generated `G` (import (J) of `cd-two-torsion-quotient-out-embedding-proof`). `U` is projective, so
`K` is a direct summand of `U^d`, finitely generated projective of dimension `d − 1`. The proof of
item 1 embeds `U ⊗ F ≅ U^k` in `K`, so `k <= d − 1`. Suppose `k = d − 1`. The image of `U^k` is a
finitely generated submodule of `K`, hence a direct summand (J2) whose complement is finitely
generated projective of dimension `(d − 1) − k = 0`, hence zero (J1). So the image of `U ⊗ P`
contains `K`, and `H_1(G; U) = K / im(U ⊗ P) = 0`, a contradiction. So `k <= d − 2`. In particular
`P` is not free, since a free `P` would have rank at most `d − 2` and be finitely generated, making
`G` of type `FP_2`.

(b) An aspherical presentation `⟨x_1..x_d | R⟩` gives the cellular resolution
`0 → Z[G]^(R) → Z[G]^d → Z[G] → Z → 0` of the aspherical presentation complex. Its second
syzygy is free, contradicting (a) as in item 1: `G` would be of type `FL`, hence `FP_2`. For a
2-complex with finitely many 0-cells and 1-cells, item 2 applies with `n = 2` and gives the same
contradiction.

(c) `(Asph) ⇒ (F)`: by (b), the second syzygy of an aspherical presentation is free.
`(F) ⇒` Kropholler's question for cd at most 2: if `P` is free for some finite generating set,
then by item 1 `G` is of type `FL`, so `FP_2`, so `G ≅ BS(1,m)` by item 4 of
`amenable-fp-iff-affiliated-top-homology-vanishes`. That item also records that the finitely
generated case of cd at most 2 is the whole of Kropholler's question in cd at most 2.
Kropholler's question for cd at most 2 `⇒ (Asph)`: every finitely generated amenable cd-2 group is
then `BS(1,m) = ⟨a, t | t a t⁻¹ a^{-m}⟩`, a one-relator presentation whose relator is not a proper
power. By Lyndon's identity theorem such a presentation is aspherical (R. Lyndon, Ann. of Math. 52
(1950); recalled). ∎

## Item 4

Let `Γ = ⟨x_1..x_d | R⟩` be aspherical with `R` infinite, and `R_0 ⊆ R` finite. As in item 1,
`H_2(Γ; U(Γ)) = ker(U^(R) → U^d)`, which contains `ker(U^(R_0) → U^d)`. That kernel has dimension
at least `|R_0| − d` by additivity (J1). Letting `|R_0| → ∞` gives `b_2^(2)(Γ) = ∞`.

For the Ollivier–Wise group over the Grigorchuk group, the presentation is `C'(1/6)` on finitely
many generators. After removing proper powers and repeated relators up to conjugacy and inversion,
it is aspherical (Chiswell–Collins–Huebschmann; recalled, not re-checked). `R` is infinite because
`Γ` is not `FP_2`, by the remark in `cd-two-kazhdan-kernel-with-grigorchuk-quotient`. ∎

## Calibration

- `Z²`, `BS(1,m)` and the Klein bottle group have one-relator aspherical presentations with
  `d = 2` and `|R| = 1 = d − 1`, as item 1 forces for amenable groups (`χ = 0`).
- `Z ≀ Z` is amenable, finitely generated and not `FP_2`, but `cd = ∞`, so it has no
  finite-dimensional `K(G,1)` at all. Item 1 does not apply, and nothing is contradicted.
- Non-amenable aspherical infinite presentations exist (item 4), and item 1 does not apply to
  them because `b_2^(2) = ∞ ≠ 0`. So the dimension-zero hypothesis is used exactly at Lemma 1.
