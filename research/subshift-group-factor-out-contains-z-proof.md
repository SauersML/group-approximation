---
rg: 2
id: subshift-group-factor-out-contains-z-proof
kind: route
title: The half-orbit index separates the diagonal automorphisms, the centralizer of G_X is trivial, and ICC injectivity lifts them to L(G_X)
target: subshift-group-factor-out-contains-z
requires:
  - subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy
  - simple-kazhdan-lef-group-from-minimal-subshift
  - icc-group-out-injects-into-group-factor-out
artifacts:
  - research/artifacts/sk-vn-rigidity-2026-09-14.md
---

Notation: `R = LC(X,F_2) ⋊_T Z` for an infinite minimal subshift `X`, `G = G_X = EL_3(R)`, `d_k = diag(u^k,1,1)`.

**Step 1: `θ_k` is an automorphism of `G`.** For `i ≠ j`, `d_k e_ij(r) d_k^{-1} = e_ij(a_i r a_j^{-1})`, where `a = (u^k,1,1)`.
So `d_k` maps the generators of `G` into `G`, as does `d_k^{-1} = d_{-k}`, and `θ_k = Ad(d_k)|_G` is an automorphism
with `θ_kθ_l = θ_{k+l}`.

**Step 2: the centralizer of `G` in `GL_3(R)` is `{I}`.**
- If `g ∈ GL_3(R)` commutes with every `e_ij(r)`, then taking `r = 1` in `g·rE_ij = rE_ij·g` gives `g_pi = 0` for `p ≠ i`
  and `g_jq = 0` for `q ≠ j`. So `g = diag(c_1,c_2,c_3)`, and comparing entries gives `c_i r = r c_j` for all `r`.
- With `r = 1`, `c := c_1 = c_2 = c_3`, and `c` is central in `R`.
- The centre of `R` is `F_2`:
  - Suppose `z = Σ_k f_k u^k` is central.
  - Commuting with `g ∈ LC(X,F_2)` gives `f_k(g∘T^{-k} − g) = 0` for all `g`.
  - For `k ≠ 0`, every point is moved by `T^k`, since `X` is infinite and minimal and so has no periodic points. So some clopen
    `g` separates `x` from `T^{-k}x`, and `f_k(x) = 0`.
  - Commuting with `u` gives `f_0∘T^{-1} = f_0`, so `f_0` is constant by minimality.
- `F_2^× = {1}` gives `g = I`.

**Step 3: `θ_k` is outer for `k ≠ 0`.**
- `θ_k = Ad(h)|_G` with `h ∈ G` means `h^{-1}d_k` centralizes `G`. By Step 2 this forces `d_k = h ∈ G`.
- By `subshift-el3-diagonal-recognition-fails-up-to-g-conjugacy` (item 1, reviewed sk-verify-16), the half-orbit index is a
  homomorphism `ind: GL_3(R) → Z` vanishing on `E_3(R)`, with `ind(d_1) = −1`. So `ind(d_k) = −k ≠ 0`, `d_k ∉ G`, and
  `θ_k` is outer.
- As `θ_kθ_l^{-1} = θ_{k−l}`, the classes `[θ_k]` are pairwise distinct, which gives (1).

**Step 4: lift to `L(G)`.**
- `G` is infinite and simple (`simple-kazhdan-lef-group-from-minimal-subshift`), hence ICC. A nontrivial finite conjugacy
  class would give a proper finite-index centralizer, whose normal core is a proper finite-index normal subgroup; there is none.
- By `icc-group-out-injects-into-group-factor-out` with trivial character, `Out(G) → Out(L(G))` is injective. Composing
  with (1) gives (2).

**Model tests.**
- For a periodic subshift, Step 2 fails: the centre of `R` contains `F_2[u^p]`, and the claim is not asserted.
- For `d = uI_3`, Step 3 would need `ind(uI_3) = −3 ≠ 0`, consistent with item 1 of the imported node.
- `θ_k` for `k = 0` is the identity.

Import used only through Step 4: Connes's countability of `Out` for property (T) factors, recalled (not read at source).
It is not needed for (1)–(2).
