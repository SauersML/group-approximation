---
rg: 2
id: lamplighter-bernoulli-crossed-products-simple-kazhdan-lef
kind: claim
title: For every finitely generated infinite LEF group Δ, EL_n over the binary crossed product of the lamplighter action of Z/2 ≀ Δ on 2^Δ is infinite simple Kazhdan LEF
distinct_from:
  window-lef-subshifts-give-matricial-crossed-products: that needs a free subshift with partial models, and minimal ones over non-RF groups are not known; this uses the topologically free lamplighter action, where minimality is automatic and every configuration is legal.
  residually-finite-group-toeplitz-elementary-groups-lef-kazhdan: that is one Toeplitz subshift per residually finite acting group; this is every LEF acting group, through Z/2 ≀ Δ on 2^Δ.
  finite-model-subshift-elementary-groups-simple-kazhdan-lef: that is free minimal subshifts with finite models, which forces residually finite groups; this acts only topologically freely and simplicity comes from Steinberg groupoid simplicity.
artifacts:
  - research/artifacts/sk-universal-embedding-b-lamplighter-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Δ` be a finitely generated, infinite, LEF group.
- `Δ` acts on `Z = 2^Δ` by `(δx)(h) = x(δ^(-1)h)`, and `a` flips the coordinate at `e`.
- `L = ⟨Δ, a⟩ ≅ Z/2 ≀ Δ` and `R = LC(Z, F_2) ⋊ L`.

Then:
1. `L ↷ Z` is minimal and topologically free (not free), and `R` is a finitely generated simple ring with `Z(R) = F_2`.
2. `R` embeds unitally in `∏_ω M_(N_n)(F_2)`. The models are `E_n = 2^(Q_n) × Q_n` for LEF models `(Q_n, φ_n)` of `Δ`:
   `s` moves the base point and `a` flips the colour at the base point. Injectivity comes from simplicity.
3. For `n ≥ 3`, `EL_n(R)` is an infinite, finitely generated, simple group with property (T) that is LEF.
4. `ℓ ↦ diag(u_ℓ, 1, …, 1)` embeds `[L, L] ⊇ [Δ, Δ]` in `EL_n(R)`.

Case `Δ = Z`: the lamplighter group gives a witness for `infinite-simple-kazhdan-hyperlinear-group` that is not a
subshift crossed product over `Z`.

Route: `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef-proof`.

**Review (sk-verify-3, 2026-09-13): PASS.** Minimality and topological freeness, Baire density of free points, simplicity and centre, the affine partial models and their multiplicativity with injectivity from simplicity, the Steinberg criterion, EJZ, LEF through the ultraproduct and `[L,L] ↪ E_2` re-derived. See `research/artifacts/sk-review-3-2026-09-13-part6.md` §A.
