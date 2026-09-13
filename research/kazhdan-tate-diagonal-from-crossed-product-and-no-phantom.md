---
rg: 2
id: kazhdan-tate-diagonal-from-crossed-product-and-no-phantom
kind: route
title: The Tate diagonal is a KK^G-equivalence once its crossed product is and the norm's Tate part has no phantom
target: kazhdan-group-algebra-tate-diagonal-is-kkg-equivalence
requires: [kazhdan-tate-crossed-product-inclusion-is-kk-equivalence, kazhdan-group-algebra-tate-part-has-no-phantom, tate-diagonal-cone-is-weakly-contractible-wreath-object, zp-restriction-trivial-splits-cellular-plus-phantom]
artifacts: [research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part2.md]
---

Let `Z_Γ = cone(T(Δ))`, so that `Res Z_Γ ≃ 0`. By item 3 of
`zp-restriction-trivial-splits-cellular-plus-phantom`, `Z_Γ ≅ eZ_Γ ⊕ (1 − e)Z_Γ`.

- **The cellular summand.** `eZ_Γ` is a retract of `τ(Z_Γ ⋊ G)`. By
  `tate-diagonal-cone-is-weakly-contractible-wreath-object`, item 2, `Z_Γ ⋊ G ≅ W ⋉_r Y`, and this
  vanishes by the first requirement.
- **The phantom summand.** `(1 − e)Z_Γ` is the phantom part of `1_T ⊗ C*_r(Γ^p)`. This is phantom
  transfer, `research/artifacts/uct-kk-norm-functor-2026-09-13-part3.md` Lemma 2 and Corollary 3: the
  source of `T(Δ)` has `θ = 1`. It vanishes by the second requirement.

So `Z_Γ ≃ 0`, i.e. `T(Δ)` is a `KK^G`-equivalence. The details are in §6 of the artifact.
