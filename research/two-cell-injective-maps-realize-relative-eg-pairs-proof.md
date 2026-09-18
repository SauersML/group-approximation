---
rg: 2
id: two-cell-injective-maps-realize-relative-eg-pairs-proof
kind: route
title: Delete the image 2-cells and reattach them at the top of the mapping cylinder of the 1-skeleton map; blow up cone vertices by universal covers; read off purity from Tor_1 of the augmentation ideal; apply Lyndon asphericity to w-discs
target: two-cell-injective-maps-realize-relative-eg-pairs
requires:
  - relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two
  - relative-eg-pair-base-meets-its-conjugates-in-free-groups
---

Facts (F2) (a `π_1`-injective subcomplex of an aspherical 2-complex is aspherical), (F3) (covers of subcomplexes) and (F4) (gluing theorem: R. Brown, *Topology and Groupoids*, 7.5.7) are those listed in `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two-proof`. Base points are carried along and omitted.

## Part 1

### (a) ⇒ (b)
The inclusion of the witnessing subcomplex is a 2-cell-injective combinatorial map.

### (b) ⇒ (a): the collapse

Let `f: K → X` be as in (b). Let `E` be the set of 2-cells of `K`, and for `e ∈ E` let `φ_e: S^1 → K^1` be its attaching map.

1. **Delete the image cells.** `X^- := X ∖ ⋃_{e∈E} f(\mathrm{int}\, e)` is a subcomplex containing `X^1`. By 2-cell-injectivity, `X` is `X^-` with one 2-cell `f(e)` attached for each `e ∈ E`, along `Φ_{f(e)}|_{S^1}`.
2. **The cylinder.** `f(K^1) ⊆ X^1 ⊆ X^-`. Let `M = X^- ∪_{f|K^1 × 0} (K^1 × [0,1])` be the mapping cylinder of `f|_{K^1}: K^1 → X^-`, with retraction `r: M → X^-`, a homotopy equivalence.
3. **The new complex.** Let `X' = M ∪ ⋃_{e∈E} D^2_e`, with `D^2_e` attached along `φ_e × 1: S^1 → K^1 × 1`. Then:
   - `X'` is a 2-dimensional CW complex;
   - `K^1 × 1` together with the discs `D^2_e` is a subcomplex isomorphic to `K`.
4. **Homotopy type.** Let `X''` be `X^-` with the discs attached along `r ∘ (φ_e × 1) = f ∘ φ_e`.
   - By combinatoriality, `f ∘ φ_e = Φ_{f(e)} ∘ h_e|_{S^1}` with `h_e` a homeomorphism of the disc. So `X'' ≅ X` by the reparametrizations `h_e`.
   - The map `X' → X''` given by `r` on `M` and the identity on the discs is a homotopy equivalence by (F4): both are adjunction spaces along the cofibration `⊔ S^1 ↪ ⊔ D^2`, and they are related by the homotopy equivalence `r`.
   - Hence `X'` is aspherical with `π_1 X' ≅ G`.
5. **Fundamental group.** The composite `K ≅ (K^1×1 ∪ ⋃ D^2_e) ↪ X' → X'' ≅ X` is `f`:
   - on `K^1` it is `r` restricted to level `1`, which is `f`;
   - on a 2-cell `e` it is `Φ_{f(e)} ∘ h_e = f ∘ Φ_e`.
   So `K ↪ X'` induces `f_* = (H ≤ G)`, and `K ⊆ X'` witnesses `RP(H,G)`. ∎

### (a) ⇒ (c)
Let `K ⊆ X` witness (a), and let `p: X_H → X` be the cover for `H`. By (F3), the component `K̂` of `p^{-1}(K)` through the base lift covers `K` with group `H ∩ H = H = π_1 K`. So `K̂ → K` is an isomorphism, and `π_1 K̂ → π_1 X_H = H` is the identity. `K̂` contains exactly one lift of each 2-cell of `K` and no lift of any other 2-cell.

### (c) ⇒ (b)
`p|_K: K → X` is combinatorial (as a covering map is) and 2-cell-injective by hypothesis. Its effect on `π_1` is `π_1 K ≅ π_1 X_H = H ≤ G`. `K` is aspherical by (F2) applied inside `X_H`, so it is a 2-dimensional `K(H,1)`.

### (a) ⇒ (d)
Take `X̃` the universal cover of the witness `X`, and `C` the component of the preimage of `K` stabilized by `H`. It is the universal cover of `K`, hence contractible, and distinct translates `gC` (`g ∉ H`) are distinct components, so they are disjoint.

### (d) ⇒ (b)
`H` acts freely on the contractible `C`, so `C/H` is a 2-dimensional `K(H,1)`.

- The map `f: C/H ⊆ X̃/H → X̃/G` is a subcomplex inclusion followed by a covering, so it is combinatorial. It induces `H ≤ G` on `π_1`.
- **2-cell-injectivity.** Suppose 2-cells `e, e'` of `C` have the same image. Then `e' = ge` for some `g ∈ G`, so `e'` lies in both `C` and `gC`. By hypothesis `g ∈ H`, so `He = He'`. ∎

### (a) ⇒ (e): cone off
Let `C` be as in (a) ⇒ (d). The translates `gC` are pairwise disjoint contractible subcomplexes.

- **The quotient.** Collapse each `gC` to its own point, giving `Y`. The quotient map is a homotopy equivalence; this is Hatcher, Prop. 0.17, with the same proof for a disjoint family. Each component deformation retracts onto a vertex, and homotopy extension applies to their union. So `Y` is contractible and 2-dimensional.
- **The action.** `G` acts cellularly on `Y`. The point from `gC` has stabilizer `gHg^{-1}`. Every other cell comes from a cell of `X̃` outside `G·C`, so it is freely permuted.
- A 2-dimensional `K(H,1)` is `K` itself.

### (e) ⇒ (a): blow up
Let `v` be a cone vertex with stabilizer `H`, `K` a 2-dimensional `K(H,1)`, `K̃` its universal cover with a base vertex `k_0`.

1. **Edge-loop attaching maps.** Homotope the attaching map of one representative in each (free) orbit of 2-cells to an edge loop or a constant loop at a vertex (cellular approximation), and translate. Attaching along homotopic maps changes `Y` only up to homotopy equivalence, and it preserves the action and the stabilizers. So we may assume every 2-cell is attached along an edge loop or constant loop.
2. **Blow up the vertices.** Let `Y'^0` be the free vertices of `Y` together with the vertices of `G ×_H K̃`, i.e. of the translates `gK̃`, one for each coset `gH`, replacing `gv`.
   - Put in the edges of `G ×_H K̃`.
   - For each edge orbit of `Y` choose a representative `ε`. An endpoint of `ε` that is a free vertex is kept. An endpoint `g v` is replaced by `g k_0` for a chosen coset representative `g`. Translate to the whole (free) orbit.
3. **Reattach 2-cells.** For a representative 2-cell with edge loop `ε_1 ⋯ ε_n`: wherever consecutive edges meet at a cone vertex `gv`, their new ends are two vertices of the connected `gK̃`. Insert an edge path in `gK̃^1` between them. Attach the 2-cell along the resulting loop, and translate.
4. **The free complex.** `Y'` is a 2-dimensional complex on which `G` acts freely: on `G ×_H K̃` because `H` acts freely on `K̃`, and on the other cells by construction.
5. **Contractibility.** Collapsing each `gK̃` to a point is a homotopy equivalence, as in (a) ⇒ (e). The result is `Y` with each attaching loop replaced by a reparametrization that pauses at the collapsed vertices. That loop is homotopic to the old one, so the result is homotopy equivalent to `Y`. Hence `Y'` is contractible.
6. **Conclusion.** `X' = Y'/G` is a 2-dimensional `K(G,1)`. It contains `(G ×_H K̃)/G ≅ K̃/H = K` as a subcomplex, whose `π_1` image is the stabilizer `H` of the component `K̃`. ∎

## Part 2: purity

Take a projective resolution `0 → P_1 → P_0 → I_{G/H} → 0` and apply `Tor^{ZG}_*(−,Z)` to `0 → I_{G/H} → Z[G/H] → Z → 0`, with Shapiro `Tor_n(Z[G/H],Z) = H_n(H)`. This gives the exact sequence

`0 = Tor_2(I,Z) → H_2(H) → H_2(G) → Tor_1(I,Z)`.

- `Tor_1(I,Z) = ker(P_1 ⊗_G Z → P_0 ⊗_G Z)`.
- `P_1 ⊗_G Z` is a projective, hence free, abelian group, and subgroups of free abelian groups are free abelian (Dedekind; any rank).
- So the cokernel of the injection `H_2(H) → H_2(G)` embeds in a free abelian group, hence is free abelian. ∎

## Part 3: one-relator groups

`w` is not a proper power, so the presentation complex `X` is aspherical (Lyndon 1950; Cockcroft 1954) and `G` is torsion-free.

### (3a)
- `H_2(G) = Z_2(X) = ker(∂: Ze → C_1)`, and `∂e = Σ_s (\text{exponent sum of } s \text{ in } w)\, s`. So `H_2(G) ≅ Z` if `w ∈ [F,F]`, and `0` otherwise.
- By Part 2, `H_2(H)` injects with free abelian cokernel.
  - If `H_2(G) = 0`, then `H_2(H) = 0`.
  - If `H_2(G) = Z`, the image is `nZ` with `Z/nZ` torsion-free, so `n ∈ {0,1}`. `n = 0` gives `H_2(H) = 0` by injectivity. `n = 1` gives an isomorphism.
- A closed orientable surface group has `H_2 = Z ≠ 0`, giving the stated consequences.
- **Calibration.** For a surface subgroup of finite index `d` in a surface group, the degree is `d`. So (3a) reproves that proper finite-index bases fail, in agreement with Corollary 3 of `relative-eg-pair-base-meets-its-conjugates-in-free-groups`. ∎

### (3b)
Let `λ: Γ → R_S` be the labelling and `K = Γ ∪_u D^2`.

- **The map.** Define `f: K → X` by `λ` on `Γ`. `λ ∘ u` is the attaching path of the unique 2-cell `e`, because `u` reads `w`, so `f` extends over the disc homeomorphically onto `e`. So `f` is combinatorial, and it is 2-cell-injective because `K` has one 2-cell.
- **Asphericity of `K`.**
  - Collapsing a maximal tree `T` of `Γ` is a homotopy equivalence. `K/T` is a rose with one disc attached along a word `ū` in the free basis of `π_1 Γ`.
  - `λ_*: π_1 Γ → F(S)` sends `[u]` to a conjugate of `w`. If `[u] = v^k` with `|k| ≥ 2`, then `w` is conjugate to `λ_*(v)^k`, so `w` is a proper power, which is excluded. If `[u] = 1`, then `w = 1`.
  - So `ū` is a nontrivial non-proper-power, and `K/T` is aspherical by Lyndon's theorem. This holds for a basis of any rank: `ū` involves finitely many basis elements, and `K/T` is a finite one-relator complex wedged with circles.
- **Conclusion.** `π_1 K = π_1Γ/⟨⟨u⟩⟩ → G` is injective with image `H` by hypothesis. Part 1 (b) ⇒ (a) gives `RP(H,G)`. ∎

## Calibration

- **Free `H`.** Any cellular map from a graph is vacuously 2-cell-injective. After homotoping a free-basis map `Γ → X^1` to a combinatorial one (subdividing `Γ`), (b) ⇒ (a) re-proves Lemma 1 of `continuous-free-chain-unions-have-gd-two-proof`.
- **Klein bottle.** Take `X` the one-square Klein bottle and `H = Z^2` of index 2. Any `π_1`-isomorphic subcomplex of the torus cover `X_H` (two squares) must carry `H_2(X_H) = Z`, whose generator uses both squares. So (c) fails for this `X`, as it must, since `RP` fails.
- **Surface group, finite index.** A w-disc for a finite-index surface subgroup of `⟨a,b,c,d | [a,b][c,d]⟩` would give degree `1` on `H_2`, but the degree is the index. So (3b) never applies there, consistent with (3a).
