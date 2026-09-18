---
rg: 2
id: product-substitution-full-groups-satisfy-boone-higman-proof
kind: route
title: Tensor-product SFT of the stationary Bratteli--Vershik models, with coordinatewise non-stacking of singular germs
target: product-substitution-full-groups-satisfy-boone-higman
requires:
  - substitution-subshifts-have-stationary-bv-models
  - stationary-vershik-maps-generate-contracting-rsgs
  - contracting-rsgs-embed-in-fp-simple-groups
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

Take `d = 2`; the general case only changes notation.

1. **Models.** By `substitution-subshifts-have-stationary-bv-models`, `(X_i, S_i)` is
   isomorphic to the Vershik system `(E_i, T_i)`, where `E_i = C_{rho_i} ⊆ Sigma_{Gamma_i}`
   as in `stationary-vershik-maps-generate-contracting-rsgs` (read substitution
   `sigma_i`, primitive, lengths `>= 2`, constant first letter `l_i` and last letter
   `r_i`). So `[[Z^2 ↷ X]] ≅ [[Z^2 ↷ E_1 × E_2]]` for the action by `T_1 × id` and
   `id × T_2`.
2. **Tensor SFT.** Let `Gamma = Gamma_1 ⊗ Gamma_2`: its nodes are pairs of nodes and
   its edges are pairs of edges, with `o(e_1,e_2) = (o e_1, o e_2)` and
   `t(e_1,e_2) = (t e_1, t e_2)`. Paths of length `n` are pairs of paths of length
   `n`, so `E = C_{(rho_1, rho_2)} ≅ E_1 × E_2`, and product cones of equal depth are
   exactly the cones.
   - The induced subgraph on `A_1 × A_2` has adjacency matrix `M_1 ⊗ M_2`. Each `M_i`
     is primitive because `sigma_i` is, and a tensor product of primitive matrices is
     primitive, since `(M_1 ⊗ M_2)^n = M_1^n ⊗ M_2^n`.
   - So that subgraph is strongly connected and not a cycle. All root edges end in it,
     so `Sigma_Gamma` has an irreducible core.
   - A canonical similarity of `Gamma`, `(β_1,β_2)ω ↦ (β_1',β_2')ω`, acts in each
     coordinate as a canonical similarity of `Gamma_i`, with depth changes
     `|β_1'| - |β_1| = |β_2'| - |β_2|`. In particular it preserves each coordinate's
     tail.
3. **Generators are rational.** Consider `T_1 × id` at a cone `(α_1, α_2)` of depth `k`.
   - If `α_1` has a non-maximal edge, it is a canonical similarity
     `(α_1,α_2) ↦ (α_1',α_2)`.
   - If `α_1 = M_1(v,k)`, Step 2 of `stationary-vershik-maps-generate-contracting-rsgs-proof`
     gives `T_1(α_1 ω_1) = P_k τ_v(ω_1)` with `|P_k| = k-1`. So
     `(T_1×id)((α_1,α_2)(ω_1,ω_2)) = (P_k, α_2[1..k-1]) · (τ_v(ω_1), α_2[k] ω_2)`.
   - The local action is therefore `(ω_1, ω_2) ↦ (τ_v(ω_1), e·ω_2)` with
     `e = α_2[k]`, followed by removing a bounded common prefix. It depends only on
     `v`, the edge `e`, and that prefix length, so there are finitely many local
     actions. `id × T_2` is symmetric.
4. **Non-stacking, coordinatewise.** The two germ facts of Step 4 of the one-dimensional
   proof hold in each coordinate.
   - (a) No canonical similarity of `Gamma` sends a point whose `i`-th coordinate is
     `x_min^i` to one whose `i`-th coordinate is `x_max^i`: tails are preserved
     coordinatewise, and the minimal and maximal tail edges differ.
   - (b) Let `c = (x_min^1[1..K], β_2)ζ ↦ (x_min^1[1..K+δ], β_2')ζ` fix the first
     coordinate's tail. Then `(T_1^{-1}×id) c (T_1×id)` is, on each cone
     `(x_max^1[1..m], α_2[1..m])` with `α_2[1..K] = β_2` and `m > K`, the canonical
     similarity onto `(x_max^1[1..m+δ], β_2' α_2[K+1..m])`. Substitute the formula of
     Step 3 and the inverse formula `T_1^{-1}(x_min^1[1..j] τ_v(ω)) = x_max^1[1..j+1] ω`;
     both lengths come out as `m + δ`. The symmetric statements hold for `T_1 c T_1^{-1}`
     and for coordinate 2.
5. **Normal form, by induction on word length.** Every `g` in
   `G_0 = <V_{Gamma,E}, T_1×id, id×T_2>` is, near each point `x`, of the form
   `c_1 ∘ (T_1^{ε_1} × T_2^{ε_2}) ∘ c_2`. Here `ε_i ∈ {-1,0,1}`, the `c_j` are canonical
   similarities, and `c_2(x)` has `i`-th coordinate `x_max^i` if `ε_i = 1` and
   `x_min^i` if `ε_i = -1`.
   - Multiplying by a generator of `V` composes canonical-similarity germs.
   - Multiplying by `T_1×id` at `x` with first coordinate `≠ x_max^1` is a
     similarity germ.
   - At first coordinate `x_max^1`, the point `(T_1×id)(x)` has first coordinate
     `x_min^1`. There `g` has `ε_1 ∈ {0, -1}` by 4(a).
     - If `ε_1 = 0`, the new exponent is `1`.
     - If `ε_1 = -1`, write `T_1^{-1} × T_2^{ε_2} = (id × T_2^{ε_2})(T_1^{-1} × id)`
       and apply 4(b): `g(T_1×id) = c_1 (id×T_2^{ε_2}) c` with `c` a canonical
       similarity. That is the normal form with `ε_1 = 0`.
   - The other generators are symmetric.
6. **Finite nucleus.** By compactness, `g` is covered by finitely many cones in normal
   form. So every local action of `g` at a deep cone is a local action of some
   `T_1^{ε_1} × T_2^{ε_2}` at a deep cone.
   - By Step 3 these are pairs of maps from `{id} ∪ Nuc_{T_i} ∪ Nuc_{T_i^{-1}}`, one
     per coordinate, together with a prefix transfer of length at most 2 between the
     coordinates (depth changes lie in `{-1,0,1}`).
   - That set is finite and does not depend on `g`. So `G_0 ⊇ V_{Gamma,E}` is a
     contracting RSG.
7. **Host.** Every element of `[[Z^2 ↷ E]]` locally agrees with some
   `T_1^a × T_2^b ∈ G_0`. By the Consequence of `contracting-rsgs-embed-in-fp-simple-groups`
   (BBMZ Prop. `NucleusHasProperties`, Thm `RSGCharacterization`,
   Prop. `contr_to_simple`), `[[Z^2 ↷ E]]` lies in the full contracting RSG `G_N` and
   embeds in the finitely presented simple group `SV_{G_N}`.
