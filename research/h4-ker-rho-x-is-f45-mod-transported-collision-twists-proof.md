---
rg: 2
id: h4-ker-rho-x-is-f45-mod-transported-collision-twists-proof
kind: route
title: Add the 106 collision walls to make ℓ_x modular, use the Fadell–Neuwirth-type bundle and its section, then remove the collision walls again by a semidirect quotient with no defect
target: h4-ker-rho-x-is-f45-mod-transported-collision-twists
requires:
  - h4-case1-pure-normal-form-and-fibred-obstruction
  - h4-case1-vertex-centres-fail-by-orthogonal-parabolics
artifacts:
  - experiments/h4-collision-2026-09-19/exact.py
  - experiments/h4-collision-2026-09-19/exact.log
  - experiments/h4-collision-2026-09-19/small.log
  - experiments/h4-collision-2026-09-19/H4_flats.txt
  - experiments/h4-collision-2026-09-19/H3_flats.txt
  - experiments/h4-collision-2026-09-19/dwalls.py
  - experiments/h4-collision-2026-09-19/roots.py
---

Notation is as in the target. For a wall `h`, write `h(·)` for its linear form. `L = L_X = ℂℓ` and `p : V → V/L`.

**Step 1 (census; `exact.py`, `exact.log`).**
- Roots are generated exactly in `ℤ[φ]`, by BFS over the simple reflections with Gram matrix `2B`. Walls are
  the covectors `C = 2B·r`.
- The rank-2 flats are the classes of pairs under "rank of `{C_i, C_j, C_k}` is 2". All ranks are computed
  by exact Gaussian elimination over `ℚ(√5)`.
- The X-walls are those with `h(ℓ) = 0`. A flat is bad when it contains none of them.
- For a bad flat `E ∋ h, h'`, the covector `h·h'(ℓ) − h'·h(ℓ)` vanishes on `E` and on `ℓ`. So it defines
  `D_E = E + L`, which is a hyperplane because `ℓ ∉ E`.
- The script asserts that no `D_E` is an X-wall. That rules out a wall of `𝒜` too, since every wall
  containing `ℓ` is an X-wall. It prints the counts of the claim.
- `H4_flats.txt` confirms two facts:
  - Each F-wall lies in 10 + 5 + 1 bad flats (sizes 2, 3, 5).
  - Distinct bad flats on a common `D` have disjoint wall sets.

  The disjointness also follows from Step 3(a) below. At most 10 punctures lie in clusters over one `D`.

**Step 2 (modularity).**
- `L` is modular in `𝒜°` when every intersection `H ∩ H'` of two walls not containing `L` lies in a wall of
  `𝒜°` that does contain `L`.
- Take `H, H'` among the 45 non-X walls. Their intersection `E₀ = H ∩ H'` is a rank-2 flat, and `E₀ + L` is
  the only candidate for that wall.
  - If `E₀` lies in an X-wall `H_x`, then `H_x ⊇ E₀ + L`, so `H_x = E₀ + L`.
  - Otherwise `E₀` is bad, and `E₀ + L = D_{E₀}` by construction.
- `exact.py` re-checks this pair by pair for all 990 pairs, exactly.
- By Terao's fibration theorem for a rank-1 modular element, `p : M° → M_X°` is a locally trivial fibre
  bundle. Here `M_X° = V/L ∖ (15 X-planes ∪ 106 collision planes)`.
- Its fibre over `b` is `b + L` with the points `y_h(b) = −h(b)/h(ℓ)` removed, one for each of the 45 non-X
  walls `h`.
- Directly: `y_h(b) = y_{h'}(b)` if and only if `b + L` meets `H_h ∩ H_{h'}`, that is `b ∈ (H_h ∩ H_{h'}) + L`,
  which is a wall of `𝒜°_L`. So over `M_X°` the 45 points stay distinct, and the fibre is `ℂ` minus 45
  points.

**Step 3 (section and parabolic).**
- Let `c > max_h ‖h‖/|h(ℓ)|` over the non-X walls. For `b ∈ M_X`, put `σ(b) = b̃ + c|b|ℓ`, where `b̃` is the
  orthogonal lift of `b`.
- Then `h(σ(b)) = h(b̃) + c|b|h(ℓ) ≠ 0` for every non-X `h`, since `|h(b̃)| ≤ ‖h‖|b| < c|b||h(ℓ)|`. For an X-wall,
  `h(σ(b)) = h(b̃) ≠ 0`.
- So `σ : M_X → M` is a continuous section of `p`, and it restricts to a section `M_X° → M°`.
- `M` is invariant under `ℝ_{>0}`. The map `σ(b)/(c|b|) = ℓ + b̃/(c|b|)` stays in the `1/c`-ball around `ℓ`,
  and there `M` agrees with `M_X` × (ball). This is the local complement at the generic point `ℓ` of the
  flat `L`, whose local walls are exactly the X-walls.
- Hence `σ_*` is the local-to-global map at `ℓ`, and its image is the standard parabolic `P_X`, up to the
  usual choice of base path. `p_* ∘ σ_* = id` recovers `ρ_X|P_X = id`.
- So `G° := π_1(M°) = F_45 ⋊_μ B°`, with `B° = π_1(M_X°)`, `F_45` the fibre group and `μ` the monodromy.

**Step 3(a) (local monodromy at a collision wall).**
- Fix `D = D_E` and a generic `b_0 ∈ D/L`. The punctures that collide at `b_0` are the pairs `h, h'` with
  `H_h ∩ H_{h'} ⊂ D`, that is the pairs inside bad flats contained in `D`.
- A good flat `E₀ ⊂ D` would give an X-wall containing `E₀ + L = D`. That is excluded by Step 1.
- Two bad flats `E ≠ E'` in `D` cannot share a wall `h`. Otherwise all of `E ∪ E'` would collide along `D`,
  so `D ⊇ (H_h ∩ H_{h1} ∩ H_{h2}) + L` for `h1 ∈ E ∖ E'` and `h2 ∈ E' ∖ E`. But `H_h ∩ H_{h1} ∩ H_{h2}` has
  rank 3, so the right side has dimension 2, not 3, a contradiction.
- The same argument shows that the clusters of distinct flats sit at distinct points of the fibre over
  `b_0`.
- On a small transverse disc `b_0 + z·n` (`|z| ≤ ε`), the punctures of a cluster `E` move as
  `y_h = y_E + zλ_h + O(z²)`, in fact exactly linearly. The `λ_h` are pairwise distinct, because two equal
  `λ`'s would make two punctures coincide on the whole disc.
- So as `z` runs once around the circle, cluster `E` rotates rigidly by `2π` inside a small disc `Δ_E`, and
  the other punctures stay nearly fixed.
- Hence `μ(μ_D) = ∏_{E ⊂ D} T_{∂Δ_E}`, a product of Dehn twists (full twists) about disjoint curves.

**Step 4 (filling the collision walls back in).**
- `M = M° ∪ ⋃_D (D ∩ M)`. Each `D ∩ M` is a connected smooth hypersurface of `M`: it is the complement of an
  arrangement in `D`.
- So `P = G° / ⟨⟨meridians of the D's⟩⟩`, by the standard fact that removing a complex hypersurface kills
  exactly the normal closure of its meridians.
- For a meridian `μ_D ∈ B°` of `D/L`, the loop `σ(μ_D)` is a meridian of `D` in `M°`:
  - `σ` maps a small transverse disc at `b_0` to a disc meeting `D = p^{-1}(D/L)` only at `σ(b_0)`;
  - that point is generic, by the choice of `c` and `b_0`;
  - the disc meets `D` transversally with intersection number `+1`, because `p ∘ σ = id`.

  Hence `ker(G° → P) = ⟨⟨σ(𝕄)⟩⟩_{G°}`, where `𝕄 = ⟨⟨μ_D⟩⟩_{B°}` and `B°/𝕄 = π_1(M_X) = P_X`.
- **Lemma.** Let `G = F ⋊_μ B` with section `s`, and let `𝕄 ⊲ B`. Put
  `R = ⟨⟨f^{-1}μ(γ)(f) : f ∈ F, γ ∈ 𝕄⟩⟩_F`. Then `⟨⟨s(𝕄)⟩⟩_G ∩ F = R`, and
  `G/⟨⟨s(𝕄)⟩⟩ ≅ (F/R) ⋊ (B/𝕄)`.
- *Proof of the Lemma.*
  - Modulo `s(𝕄)` we have `f ≡ s(γ)fs(γ)^{-1} = μ(γ)(f)`, so `R ⊂ ⟨⟨s(𝕄)⟩⟩`.
  - `R` is `μ(B)`-invariant, since `μ(β)(f^{-1}μ(γ)f) = f'^{-1}μ(βγβ^{-1})f'` with `f' = μ(β)f`. So `R ⊲ G`.
  - In `G/R = (F/R) ⋊ B`, the subgroup `s(𝕄)` centralises `F/R` and is normal in `s(B)`, so it is normal.
  - Therefore `⟨⟨s(𝕄)⟩⟩/R = s(𝕄)`, which meets `F/R` trivially. This gives the claim. ∎
- Applied with `F = F_45` and `B = B°`, the Lemma gives `P = (F_45/R) ⋊ P_X`. Since `ρ_X = p_*` kills
  `F_45` and restricts to `id` on `σ_*B°/𝕄 = P_X`, we get `K = ker ρ_X = F_45/R`.

**Step 5 (the relators).**
- The identity `(fg)^{-1}T(fg) = g^{-1}(f^{-1}T(f))g · g^{-1}T(g)` shows that for a single `γ` it is enough
  to take `f` among free generators. It also shows that `R_{γγ'} ⊂ ⟨⟨R_γ, R_{γ'}⟩⟩` and `R_γ^{-1} = R_γ`.
  So `R` is the normal closure of the `R_{βμ_Dβ^{-1}}`, for `β ∈ B°` and `D` among the 106 collision walls.
- Choose a free basis adapted to the disjoint discs `Δ_E`, `E ⊂ D`: each puncture loop `x_h` of `E` runs
  inside `Δ_E`, and `δ_E = ∏_{h ∈ E} x_h` in cyclic order. By Step 3(a), `μ(μ_D)` fixes the generators
  outside the discs and sends `x_h ↦ δ_E x_h δ_E^{-1}` for `h ∈ E`.
- So `R_{μ_D} = ⟨⟨[δ_E, x_h] : E ⊂ D, h ∈ E⟩⟩`.
- Conjugating by `μ(β)` replaces `(δ_E, x_h)` by `(μ(β)δ_E, μ(β)x_h)`, which is the boundary loop and the
  puncture loops of the transported disc `β(Δ_E)`. This gives exactly the relators of the claim.
- For `|E| = 2`, `[x_h x_{h'}, x_h] = x_h[x_{h'}, x_h]x_h^{-1}`, which is a commutation.
- By the Lemma, no relation beyond `R` holds in `F_45 ⊂ P`.

**Step 6 (consequences).**
- **Abelianisation.** Every relator is a commutator, so `K^{ab} = F_45^{ab} = ℤ^{45}`.
- **ℤ² through each F-generator.** Let `f` be an F-wall and `E = {f, h}` one of its 10 bad `A_1×A_1` flats.
  - At a generic point `e ∈ E`, the local fundamental group is `⟨m_f, m_h⟩ ≅ ℤ²`. It maps injectively,
    because its image in `H_1(M) = ℤ^{60}` is `ℤ e_f ⊕ ℤ e_h`.
  - `p(e) ∈ M_X`, because `e` lies on no X-wall. So a small ball around `e` projects into a contractible ball
    of `M_X`, and after any base path `⟨m_f, m_h⟩ ⊂ K`, since `K ⊲ P`.
  - `H_f ∩ M` is connected, so `m_f` is `P`-conjugate to the generator `P_i` of `F` that is the meridian of
    `f`, say `P_i = g m_f g^{-1}`.
  - Then `⟨P_i, g m_h g^{-1}⟩ ≅ ℤ²` lies in `K`. So `C_K(P_i)` is not cyclic, and `K` is not free.
  - In the presentation this is the relator `[x_f, x_h]^β` of Step 5.
- **(H″) in these terms.** By `h4-case1-vertex-centres-fail-by-orthogonal-parabolics` and the Helly
  reformulation it builds on, (H″) is a statement about `N ⊂ P_X` acting on `K` by conjugation. By
  Step 4, that action is `μ` on `F_45/R`, for any lift `Ñ ⊂ B°` of `N`. The lift is unique only modulo `𝕄`,
  which acts trivially on `F_45/R`.

**Step 7 (calibration; `small.log`).**
- The same code gives:
  - no bad flats for `A_3` and `A_4` (exact) or for `B_3` and `B_4` (float);
  - 5 bad `A_1×A_1` flats for `H_3` with `X = I_2(5)`, 2 of them through the F-walls, each on its own
    collision wall;
  - 547 bad flats on 319 collision walls for the `A_3`-line of `H_4` (`exact.log`, block `H4Y`).
- With no bad flats, `𝒜° = 𝒜` and `K = F_n`. That is the fibre-type case used by the type-A Helly proof.
- The `H_3` case satisfies the Case 1 analogue, by `lem:triple` as cited in the target, even though `K`
  there has `ℤ²`'s through both F-generators. So Step 6 alone does not refute (H″). ∎
