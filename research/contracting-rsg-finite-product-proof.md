---
rg: 2
id: contracting-rsg-finite-product-proof
kind: route
title: Place |F| labelled copies of E under a new root and let F permute the labels; RSG moves, rationality and the nucleus all come from H
target: contracting-rsgs-closed-under-products-with-finite-groups
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

Lane `bh-free-23`, 2026-09-18. Lane proof, elementary. Definitions as in BBMZ arXiv:2309.06224v3:
`def:rsg`, `def:contracting`, local actions `f|_α` and nuclei `Nuc_f` (Section `ssec:nuclei`),
and the irreducible core definition.

**Construction.**
- **Splitting `E`.** Write the clopen set `E` as a disjoint union of `k ≥ 2` cones
  `C_{α_1}, …, C_{α_k}`. This is possible because `E` has no isolated points: if `E` is a
  single cone, pass to the children of a branching descendant and the complementary cones.
  Put `w_j = t(α_j)`.
- **The new graph.** Let `Γ'` be `Γ` plus a new node `r'` with edges `e_{f,j} : r' → w_j` for
  `f ∈ F` and `1 ≤ j ≤ k`. Put `E' = C_{r'} = ⊔_{f,j} C_{e_{f,j}}`, and let
  `Φ : E × F → E'`, `Φ(α_j ω, f) = e_{f,j} ω`.
- **The action.** `H × F` acts on `E'` by `ρ(h,f')(Φ(x,f)) = Φ(hx, f'f)`. This action is
  faithful.

**Subshift and core.**
- `Σ_{Γ'}` has no isolated points or empty cones, since `Σ_Γ` has none and `C_{r'}` is
  nonempty.
- With `Γ_0` the core of `Γ`, the three core conditions hold for `Γ'`. The node `r'` has no
  incoming edges, every path from it enters `Γ`, and paths of length `N+1` end in `Γ_0`.

**Rationality.**
- The cone `C_{e_{f,j}β}` is `Φ(C_{α_jβ} × {f})`. For all but finitely many `(f,j,β)`, the image
  `h(C_{α_jβ})` lies inside a single `C_{α_i}`. For those, the common prefix of
  `ρ(h,f')(C_{e_{f,j}β})` is `e_{f'f,i}` followed by the corresponding path of `h`.
- So `ρ(h,f')|_{e_{f,j}β} = h|_{α_jβ}` as maps `C_{t(β)} → Σ_Γ ⊆ Σ_{Γ'}`.
- Only finitely many other local actions occur. So `ρ(h,f')` is rational, and each local action
  that occurs infinitely often lies in `Nuc_h`.

**RSG.**
- Every proper cone of `E'` has the form `C_{e_{f,j}β}` with type `t(β)` (or `w_j` when `β` is
  empty), matching `C_{α_jβ}`. Since `k ≥ 2`, the cone `C_{α_jβ}` is a proper cone of `E`.
- Given two proper cones `C_{e_{f,j}β}` and `C_{e_{f',i}γ}` of the same type, `H` contains `h`
  mapping `C_{α_jβ}` onto `C_{α_iγ}` by the canonical similarity.
- Then `ρ(h, f' f^{-1})(e_{f,j}βω) = Φ(α_iγω, f') = e_{f',i}γω`, again canonical.

**Contracting.**
- By the rationality paragraph, `Nuc_{ρ(h,f')} = Nuc_h` for every `(h,f')`: a local action
  occurs infinitely often for `ρ(h,f')` exactly when it does for `h`.
- So `Nuc_{H'} = Nuc_H`, which is finite, and together with the irreducible core `H'` is
  contracting.
- `H' = ρ(H × F) ≅ H × F`. ∎

**Remark.** The only use of `k ≥ 2` is to make every proper cone of `E'` correspond to a proper
cone of `E`. With `k = 1`, the whole copy `C_{e_{f,1}}` would have to map canonically into a
proper sub-cone, which no homeomorphism of `E` does.
