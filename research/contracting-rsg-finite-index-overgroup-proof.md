---
rg: 2
id: contracting-rsg-finite-index-overgroup-proof
kind: route
title: Induce the action to one labelled copy of E per coset; each element acts on each copy by an element of H, so rationality, the RSG moves and the nucleus all come from H
target: contracting-rsgs-closed-under-finite-index-overgroups
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

Lane `bh-free-23`, 2026-09-18. Lane proof, elementary. Definitions as in BBMZ arXiv:2309.06224v3
(`def:rsg`, `def:contracting`, the local actions and nuclei of `ssec:nuclei`, and the
irreducible core definition). This generalizes `contracting-rsg-finite-product-proof`.

**The action.**
- **Coset data.** Fix coset representatives `t_1, …, t_k` with `G = ⊔ t_i H`. For `g ∈ G` and
  each `i`, write `g t_i = t_{σ_g(i)} h_i(g)` with `h_i(g) ∈ H`.
- **Definition.** On `{1..k} × E`, put `g·(i,x) = (σ_g(i), h_i(g)x)`. This is the standard
  induced action, and it is an action.
- **Faithfulness.** If `g` acts trivially, then `σ_g = id`, so `g ∈ ⋂_i t_i H t_i^{-1}`, and
  each `h_i(g) = t_i^{-1} g t_i` acts trivially on `E`. So `h_i(g) = 1` and `g = 1`.

**The subshift.**
- **Splitting `E`.** Write `E = C_{α_1} ⊔ … ⊔ C_{α_m}` with `m ≥ 2`. This is possible because
  `E` has no isolated points: split a cone at a branching descendant.
- **The new graph.** Let `Γ'` be `Γ` plus a new node `r'` with edges `e_{i,a} : r' → t(α_a)`,
  for `1 ≤ i ≤ k` and `1 ≤ a ≤ m`. Put `E' = C_{r'}` and identify `(i, α_a ω)` with
  `e_{i,a} ω`.
- **Irreducible core.** The core of `Γ` is still one for `Γ'`: `r'` has no incoming edges, and
  paths of length `N+1` end in the core. `Σ_{Γ'}` has no isolated points or empty cones.

**Rationality and nucleus.**
- **Deep cones.** On the cone `C_{e_{i,a}β} ≅ {i} × C_{α_aβ}`, the element `g` acts as `h_i(g)`
  into copy `σ_g(i)`. For all but finitely many `(i,a,β)`, the image `h_i(g)(C_{α_aβ})` lies in a
  single `C_{α_b}`. Then the common prefix of the image is `e_{σ_g(i),b}` followed by the rest of
  `\overline{h_i(g)}(α_aβ)`.
- **Local actions.** So `g|_{e_{i,a}β} = h_i(g)|_{α_aβ}`. Hence `g` is rational, and
  `Nuc_g = ⋃_i Nuc_{h_i(g)} ⊆ Nuc_H`.
- **Contracting.** `Nuc_{G'} ⊆ Nuc_H` is finite, and `Γ'` has an irreducible core, so `G'` is
  contracting.

**RSG moves.**
- **The cones to match.** Every proper cone of `E'` is some `C_{e_{i,a}β}`. It corresponds to the
  proper cone `C_{α_aβ} ⊊ E` (proper because `m ≥ 2`), and it has the same terminal node.
- **Choosing the element.** Given two proper cones `C_{e_{i,a}β}` and `C_{e_{j,b}γ}` with the same
  terminal node, the RSG property of `H` gives `h ∈ H` mapping `C_{α_aβ}` onto `C_{α_bγ}` by the
  canonical similarity. Put `g = t_j h t_i^{-1}`.
- **It works.** Then `g t_i = t_j h`, so `g(i, α_aβω) = (j, α_bγω)`. That is the canonical
  similarity `C_{e_{i,a}β} → C_{e_{j,b}γ}`.
- **Conclusion.** `G'`, the image of `G`, is a contracting RSG, and `G' ≅ G`. ∎
