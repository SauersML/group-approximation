# sk-lamplighter-characters: plan (2026-09-14, wave 12)

Lane sk-lamplighter-characters. The problem: character rigidity for the lamplighter hosts of the paper's Corollaries 3–4,

`G_Δ = EL_n(R_Δ)`, `R_Δ = LC(Ω,F_2) ⋊ Λ`, `Ω = F_2^Δ`, `Λ = F_2 ≀ Δ` acting by `x ↦ δx + f`, `n ≥ 3`, `Δ` infinite.

## Why the Z-case proof does not transfer verbatim
The reviewed Z-case proof (`subshift-elementary-groups-are-character-rigid`, sk-characters-rigidity-b; passed by sk-characters-rigidity-a and sk-verify-8) rests on three things:
- (Z1) Kakutani–Rokhlin towers for a **free** minimal Z-action. They give locally finite subgroups `L_y` whose finite stages mix, so supports grow linearly: Lemma 1′ uses uniform recurrence.
- (Z2) Two such subgroups generate `G`.
- (Z3) Tower groups `H_V` at far-apart small sets sit inside one `L_{y*}`.

The Λ-action on Ω is topologically free but **not free** (constant configurations are Δ-fixed), so exact clopen tower partitions of Ω with Λ-shapes do not exist.

## The replacement (the lane's idea)
- **UHF inside the host.** The lamp subgroup `K = ⊕_Δ F_2` acts FREELY by translation, and
  `R_K := LC(Ω,F_2) ⋊ K = ⋃_W M_{2^{|W|}}(F_2)` over finite `W ⊆ Δ`, with tensor-identity inclusions. So
  `L := GL_n(R_K) = ⋃ GL_{n·2^{|W|}}(F_2)` is a SINGLE-BLOCK diagonal limit: supports grow proportionally, with no recurrence needed. This replaces (Z1).
- **(Z2) replaced.** `d_δ = diag(u_δ,1,…,1)` normalizes `G_Δ`, and `G_Δ = ⟨L, d_δ^{±1} L d_δ^{∓1} : δ ∈ S_Δ⟩`. They share the abelian subgroup `e_23(LC(Ω,F_2))`, so the trivial-part projections coincide and are central.
- **(Z3) replaced.** For far-apart small sets `V_k`, the tower algebras `span{e_{aV_k}u_{ab^{-1}}}` are conjugate, by a unit `w ∈ R_Δ`, to matrix-unit systems inside `R_K`. The Bernoulli measure is Λ-invariant, so the idempotents `e_{aV_k}` have equal ranks in the UHF stages. The group `M := wLw^{-1}` is again a single-block diagonal limit inside `G_Δ`, and it contains every `H_{V_k}` and the abelian group `e_23((1−e)LC(Ω))`. Larsen–Tiep then makes the character constant on `M∖{1}`, and Bessel finishes.

## Targets
1. **Theorem L.** For every infinite group `Δ` and `n ≥ 3`, every character of `G_Δ` is `c·1 + (1−c)δ_e`. It needs no amenability, no LEF and no finite generation of Δ.
2. Consequences: `L(G_Δ)` is the only II_1 factor representation; `IRS(G_Δ)` is trivial; and with `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, `G_Δ` is sofic iff it has a nontrivial almost action (T3 of sk-sofic-host-hamming).
3. Firewalls: `F_q`, `q > 2` (centre, `K_1`); topological full groups (Dudko–Medynets characters); finite Δ.

Deliverables: proof artifact part 1, the claim and route nodes, queue lines with sk-verify-18/19.
