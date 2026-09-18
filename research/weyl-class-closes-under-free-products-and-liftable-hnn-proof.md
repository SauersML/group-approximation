---
rg: 2
id: weyl-class-closes-under-free-products-and-liftable-hnn-proof
kind: route
title: "Proof: amalgamate Lambda_1 x Sigma_2 and Sigma_1 x Lambda_2 over Sigma_1 x Sigma_2; an HNN letter that normalizes Sigma descends to an HNN extension of the Weyl group; the lift costs type F_m associated subgroups and a matching outer action"
target: weyl-class-closes-under-free-products-and-liftable-hnn
requires:
  - normalized-benign-witnesses-give-the-semidirect-join
---

Verification tier: proposed-established. Elementary Bass--Serre theory and
the standard finiteness facts:
- a graph of groups with finitely many vertices and edges, vertex groups of
  type `F_m` and edge groups of type `F_{m-1}` (in particular of type `F_m`)
  has type `F_m`; for `m = F`, finite aspherical complexes glue along finite
  aspherical subcomplexes to a finite aspherical complex;
- the quotient of a type `F_m` group by a type `F_{m-1}` normal subgroup is
  of type `F_m` (Geoghegan, *Topological Methods in Group Theory*, §7.2;
  homologically, Bieri's notes).

We use two subgroup facts, both from normal forms (Britton's lemma, and the
reduced-form theorem for amalgams):
- **(S1)** If `E ≤ A_i ≤ V_i` (`i = 1, 2`), then
  `⟨A_1, A_2⟩ ≤ V_1 *_E V_2` is `A_1 *_E A_2`. Indeed `A_i \ E ⊆ V_i \ E`, so
  alternating words are still reduced.
- **(S2)** If `A, B ≤ M ≤ V` and `θ : A -> B`, then `⟨M, t⟩ ≤ V *_θ` is
  `M *_θ`. Indeed a `t`-reduced word over `M` is `t`-reduced over `V`.

## Item 1

- **Type.** `Λ = (Λ_1 × Σ_2) *_{Σ_1 × Σ_2} (Σ_1 × Λ_2)` has vertex groups
  and edge group of type `F_m` (products of type `F_m` groups), so `Λ` is of
  type `F_m`. So is `Σ = Σ_1 × Σ_2`.
- **Normalizer.** `A_1 = M_1 × Σ_2` normalizes `Σ`, since `M_1` normalizes
  `Σ_1` and `Σ_2 ⊴ Σ_2`. Symmetrically `A_2 = Σ_1 × M_2` normalizes `Σ`.
- **The subgroup they generate.** Both `A_i` contain `E = Σ_1 × Σ_2 = Σ`.
  By (S1), `H = ⟨A_1, A_2⟩ = A_1 *_Σ A_2 ≤ N_Λ(Σ)`.
- **The quotient.** `Σ` is normal in `H`. Killing an edge group that is
  normal in both factors gives
  `H/Σ = (A_1/Σ) *_{Σ/Σ} (A_2/Σ) = (M_1/Σ_1) * (M_2/Σ_2)`.
- **Conclusion.** `G_1 * G_2 ≤ (M_1/Σ_1) * (M_2/Σ_2) ≤ N_Λ(Σ)/Σ`, since a
  free product of subgroups is a subgroup of the free product.
- **The single-letter variant.** `Λ *_Σ (Σ × ⟨s⟩)` is of type `F_m`. By
  (S1), `⟨M, Σ × ⟨s⟩⟩ = M *_Σ (Σ × ⟨s⟩)` normalizes `Σ`, and its quotient
  by `Σ` is `(M/Σ) * Z`.
- **Other factors.** A type `F_m` group `H` is Weyl with `Σ = 1`. A finite
  group `F(A)/N` is Weyl with `Λ = F(A)` and `Σ = N` of finite rank. ∎

## Item 2

- **Type.** `Λ' = ⟨Λ, t | t a t^{-1} = θ(a), a ∈ A⟩` is a graph of groups with
  vertex group `Λ` and edge group `A` of type `F_m`, so it is of type `F_m`.
- **`t` normalizes `Σ`.** `t Σ t^{-1} = θ(Σ) = Σ`.
- **The subgroup.** `A, B ≤ M`, so by (S2) `⟨M, t⟩ = M *_θ`. It normalizes
  `Σ`.
- **The quotient.** Present `M *_θ` as `(M * ⟨t⟩) / ⟨⟨t a t^{-1} θ(a)^{-1}⟩⟩`.
  Killing the normal subgroup `Σ` gives
  `(M/Σ * ⟨t⟩) / ⟨⟨t ā t^{-1} θ̄(ā)^{-1}⟩⟩ = W *_φ̄`,
  with `φ̄ : A/Σ = C_1 -> B/Σ = C_2`, the map `φ`.
- **Conclusion.** `C_1, C_2 ≤ G ≤ W`, so by (S2) for `W *_φ` we get
  `⟨G, t⟩ = G *_φ ≤ N_{Λ'}(Σ)/Σ`. ∎

## Item 3

In `(G_1 * G_2) *_φ` with `t c t^{-1} = φ(c)`, the subgroup
`⟨G_1, t^{-1} G_2 t⟩` is `G_1 *_{C_1 = t^{-1} C_2 t} t^{-1} G_2 t`, which is
`G_1 *_φ G_2`.
- This is the standard embedding of an amalgam in an HNN extension of the
  free product; it follows from Britton's lemma.
- By item 1, `G_1 * G_2 ≤ W` for the pair `Σ = Σ_1 × Σ_2`, with the lifts
  `A_1 × Σ_2` of `C_1` and `Σ_1 × A_2` of `C_2`. By the liftability
  hypothesis and item 2, the HNN extension is Weyl, hence so is its
  subgroup. ∎

## Item 4

- **(a)** `A` is of type `F_m`, and `Σ ⊴ A` is of type `F_m ⊇ F_{m-1}`, so
  `C_1 = A/Σ` is of type `F_m` by the quotient fact. The same holds for
  `B`. For `m = F`, `Λ` is torsion-free but `C_i` need not be, and the
  quotient fact gives `F_∞`.
- **(b)** For `a ∈ A` and `σ ∈ Σ`,
  `θ(a) σ θ(a)^{-1} = θ(a θ^{-1}(σ) a^{-1})`, so
  `conj(θ(a))|_Σ = θ|_Σ ∘ conj(a)|_Σ ∘ θ|_Σ^{-1}`.
  - `θ(a)` lifts `φ(ā)`, so `ρ(φ(c)) = τ ρ(c) τ^{-1}` in `Out(Σ)`.
  - For a general normalizing `t` with `t a t^{-1} = b σ_0`, `b` a lift of
    `φ(c)` and `σ_0 ∈ Σ`: `conj(b)|_Σ = conj(t) ∘ conj(a) ∘ conj(t)^{-1} ∘ inn(σ_0)^{-1}`
    on `Σ`, which gives the same identity. ∎

## Item 5

- **Finitely generated subgroups of Weyl groups are recursively presented
  (`m ≥ 2`).** Let `G = ⟨g_1, ..., g_k⟩ ≤ M/Σ` and lift `g_i` to `x_i ∈ M`.
  - A word `w` is trivial in `G` iff `w(x) ∈ Σ`.
  - `Λ` is finitely presented and `Σ` is finitely generated. So the set of
    words in the generators of `Λ` that represent elements of `Σ` is r.e.:
    enumerate the words in the generators of `Σ`, times consequences of the
    relators.
  - Hence the kernel of `F_k -> G` is r.e.
- **Closure given `U`.** If `C_1, C_2 ≤ G` are finitely generated, then
  `G *_φ` is finitely generated and recursively presented. It embeds in `U`
  (Higman), so it is Weyl if `U` is, by subgroup closure.
- **Remark on Higman's construction.** Every HNN step in the classical
  proof has an associated subgroup `L ≤ K`, with `K` finitely presented,
  witnessing the benignness of some `A = L ∩ F`.
  - To run that step through item 2 along a Weyl pair, 4(a) needs `L`, taken
    modulo `Σ`, to be of type `F_m`.
  - That is a type `F_m` witness for `A`, which is the benign statement
    being proved. So the construction is circular at exactly 4(a). ∎
