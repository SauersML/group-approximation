---
rg: 2
id: penrose-cut-torus-subshift-finite-type-proof
kind: route
title: Code the cut torus by vertex patches, then develop a colouring with legal windows into a Penrose tiling by gluing labelled rhombi into a covering of the plane
target: penrose-cut-torus-subshift-is-of-finite-type
requires:
  - penrose-tiling-group-is-an-amenable-orbit-full-group
artifacts:
  - research/artifacts/penrose-cut-torus-sft-2026-09-16.md
---

## Why sufficient

The full proof is in the artifact, §1--§4. Section 0 there lists the trust surface, and
§6 lists the weak points.

**Imports.** Chornyi--Juschenko--Nekrashevych, arXiv:1602.04255. The TeX source
`IET_copy.tex` was fetched from arXiv on 2026-09-16, and line numbers refer to it. Beyond
line 95 they differ slightly from the copy cited in `penrose-tiling-group-amenable-orbit-citation`.
- **(I1)** Lines 569--582: `F` is a fundamental domain for `Lat`, and `X ≅ F`. The
  required node adds that `Lambda` acts freely.
- **(I2)** Lines 512--527: `V''` is equidecomposable with `F`.
- **(I3)** Lines 485--500: `(s, ξ~) -> (T_ξ~, s)` is a homeomorphism `V' -> 𝒯`.
- **(I3a)** Lines 356--358: `𝒯` is a Cantor set, in particular Hausdorff, in the
  vertex-patch topology.
- **(I4)** Lines 299--315 and 336--344: the definition of Penrose tilings and of `𝒯`.
- **(I5)** Lines 464--467 and 491--498: the translation rule `x ∈ T_ξ~ ⇔ x - v' ∈ T_{ξ~+v}`
  and the vertex correspondence `x = Σ k_j ζ^j -> (Σ k_j, ξ~ + Σ k_j ζ^(2j) - Σ k_j)`.

**Steps.**
1. **Patches are locally constant** (Lemma 0). The tile-patch topology on `𝒯` is compact
   by finite local complexity, and it refines the Hausdorff vertex-patch topology (I3a).
   So the two topologies agree.
2. **Orbit correspondence** (Lemma 1).
   - Let `Θ : X -> 𝒯` be the composite of (I1)--(I3).
   - For each `x`, `ψ_x : Lambda -> V(Θ(x))` is a bijection with
     `Θ(x + λ) = Θ(x) - ψ_x(λ)`.
   - It satisfies the cocycle identity `ψ_x(λ + μ) = ψ_x(λ) + ψ_{x+λ}(μ)`, and is
     locally constant in `x`.
   - The formula is `ψ_x(λ) = s(f_λ) - s(f) + σ^(-1)(η(f_λ) - η(f))`. The translation
     rule (I5) gives item 1, and injectivity uses freeness.
3. **Coding** (Proposition 2).
   - `y_x(μ) = pat_{r_0}(Θ(x + μ))` is an equivariant embedding, since the increments
     `ψ_{x+λ}(s)` are functions of the patch at `λ`.
   - Minimality follows from density of the vertex orbits (I3a).
4. **Finite type** (§4). Let `y` have every window on a translate of `B(N)` legal. Put
   `m_* = 2M(max(D, r_0 + 2)) + 2` and `N = max(L, (m_* + 2) D')`.
   - **Positions.** `pos_y` is obtained by integrating the increments read from `y`.
     It is well defined because every relator loop lies in a window.
   - **Charts.** Each window agrees with a genuine coding `y_{x_λ}`. This gives the chart
     lemma along edge paths of length `<= m_* + 2`.
   - **Labelled rhombi.** Each patch `y(λ)` produces labelled rhombi. Claims A and B show
     that these do not depend on the vertex they are read from. By Lemma 3, near each
     label they coincide with the tiles of `Θ(x_λ)` near `0`.
   - **The covering.** Glue the rhombi along the faces spanned by common labels, giving a
     space `K`.
     - `dev : K -> C` restricts to homeomorphisms on chart regions.
     - Lemma 4: every point has a neighbourhood mapped onto a disc of radius 1.
     - `K` is Hausdorff (uses `2M(3) <= m_*`) and connected.
     - Lemma 5: `dev` is a covering of `C`, hence a homeomorphism.
   - **Conclusion.** The rhombi form an edge-to-edge tiling with matching arrows, that is,
     a Penrose tiling `T` with vertex `0`. `x* = Θ^(-1)(T)` satisfies
     `pat_{r_0}(T - pos_y(λ)) = y(λ)` and `ψ_{x*} = pos_y`, so `y = y_{x*} ∈ Y`.

**Where a referee should look first.**
- (I3a), used as "a Penrose tiling is determined by its vertex set". The artifact (§6.1)
  checks this directly on the pentagrid for regular `ξ~`, but not for singular `ξ~` or for
  the arrows.
- The point-set topology of `K` in Step 4, and the bookkeeping that every chart use stays
  within `m_*`.
