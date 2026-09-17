---
rg: 2
id: fg-groups-simple-kazhdan-hosts-lamplighter-proof
kind: route
title: The lamplighter crossed product host is simple Kazhdan for every infinite acting group, and Whitehead's lemma embeds the whole acting group
target: fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree
requires: [steinberg-elementary-groups-are-simple-mod-centre, elementary-groups-over-fg-rings-have-property-t, crossed-product-el-word-problem-is-group-wp-plus-language, property-t-implies-property-fa]
artifacts: [research/artifacts/lamplighter-kazhdan-host-without-lef-2026-09-17.md]
---

Full proof: `research/artifacts/lamplighter-kazhdan-host-without-lef-2026-09-17.md`, Steps 1-6.

1. **Dynamics.** `Δ = Γ × Z` is infinite and finitely generated. `L = Z/2 ≀ Δ`
   acts on `Z = 2^Δ` minimally (the orbit contains `x + ⊕_Δ Z/2`) and
   topologically freely (two fresh coordinates `h ≠ δ^(-1)h` outside any
   window). So `R = LC(Z,F_2) ⋊ L` is simple with `Z(R) = F_2`, and is generated
   by `u_s^(±1)`, `u_a` and `1_[x(e)=1]`. These are Lemmas 1-2 of
   `research/artifacts/sk-universal-embedding-b-lamplighter-2026-09-13.md`,
   whose proofs use only that `Δ` is infinite and finitely generated.
2. **(T).** `R` is a finitely generated ring, so `H = EL_3(R)` is Kazhdan by
   `elementary-groups-over-fg-rings-have-property-t`, and finitely generated.
   FA follows by `property-t-implies-property-fa`.
3. **Simplicity.** The transformation groupoid is ample, Hausdorff, minimal and
   effective with compact infinite unit space, so by
   `steinberg-elementary-groups-are-simple-mod-centre` every normal subgroup
   is central or everything, and the centre lies in `F_2^× I_3 = 1`.
4. **Embedding.** `Γ ≤ Δ ≤ L ↪ GL_1(R)`, and Whitehead's identity
   `w(u) w(-1) = diag(u, u^(-1))` with `w(u) = e_12(u) e_21(-u^(-1)) e_12(u)`
   gives the injective homomorphism `γ ↦ diag(u_γ, u_γ^(-1), 1)` into `H`.
5. **Word problem.** `F_x(ℓ) = (ℓ^(-1)x)(e)` realizes `Z` as an `L`-subshift
   `X`, so `WP(H) ≡_T WP(L) ⊕ L(X)` by
   `crossed-product-el-word-problem-is-group-wp-plus-language`. Normal forms
   `(c, δ)` give `WP(L) ≤_T WP(Δ)`, and since `F_x(ℓ) = x(δ) + c(δ)` on the full
   shift, pattern occurrence is a consistency test decided with `WP(Δ)`.
   `WP(Δ) ≡_T WP(Γ)`, and substitution gives `WP(Γ) ≤_m WP(H)`.
