---
rg: 2
id: subshift-el3-two-ended-lattice-stabilizers-locally-finite
kind: claim
title: G_X acts on pairs of skew lattices at +∞ and −∞ with locally finite stabilizers, while one end alone has non-amenable stabilizers
distinct_from:
  cut-stabilizers-of-el-n-are-locally-finite-normalish: that stabilizes a splitting of one orbit module; this stabilizes lattices over the completions B((u)) and B((u^{-1})), uniformly over all orbits
artifacts:
  - research/artifacts/sk-exact-gx-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `X` is an infinite minimal subshift with shift `T`, `B = LC(X,F_2)` and `α(f) = f∘T^{-1}`. Then `R = B[u^{±1};α]`, with `uf = α(f)u`, and `G_X = EL_3(R)`.
- The completions are `R̂_+ = B((u)) = {Σ_{j≥−n} f_ju^j}` and `R̂_- = B((u^{-1}))`, with `O_+ = B[[u]]` and `O_- = B[[u^{-1}]]`.
- `𝓛_±` is the countable set of left `O_±`-submodules `L ⊆ R̂_±^3` with `u^{±n}O_±^3 ⊆ L ⊆ u^{∓n}O_±^3` for some `n`, and `L/u^{±n}O_±^3` finitely generated over `B`.

**Theorem.**
1. `GL_3(R)` acts on `𝓛_+` and on `𝓛_-` by right multiplication `L ↦ Lg`.
2. The stabilizer of `O_+^3` is `GL_3(B[u;α])`, which contains `SL_3(F_2[u])`, a non-amenable subgroup of `G_X`.
3. For every `(L_+, L_-) ∈ 𝓛_+ × 𝓛_-`, the stabilizer of the pair in `G_X` is locally finite. For the standard pair it equals `G_X ∩ GL_3(B)`.

**What it changes.** The single-end Tate lattice space of `subshift-elementary-groups-are-exact` has non-amenable stabilizers. Using both ends at once makes all stabilizers amenable, as for `SL_3(F_2[u^{±1}])` acting on two Bruhat–Tits buildings. The residue ring `B` is infinite, so these lattice spaces have infinite valence. Exactness of `G_X` still needs an amenable action on a compactification, or finite decomposition complexity of a fibering over them; that part is open.

**Proof:** `subshift-el3-two-ended-lattice-stabilizers-proof`.
