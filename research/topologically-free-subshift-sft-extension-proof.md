---
rg: 2
id: topologically-free-subshift-sft-extension-proof
kind: route
title: Under topological freeness, trivially acting words have trivial formal cocycles, so the formal-cocycle SFT argument goes through
target: topologically-free-subshift-fp-subgroups-extend-to-sft
requires: []
artifacts:
  - research/artifacts/solve-fp-amenable-nonfree-hosts-2026-09-13.md
---

## Why sufficient

The argument is Theorem 2 of `research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md`,
Section 3, with one step replaced.

1. **Local rules.**
   - Each `g ∈ [[Λ ~ X]]` has, by definition, a continuous cocycle. That cocycle need not be
     unique here, so fix one.
   - A continuous map into a discrete group is locally constant. `X` is compact, so it takes
     finitely many values and depends on `x|_D` for a finite `D`.
   - So `g = T_c|_X` for a local rule `c`, where `T_c(x) = c(x|_D)·x`.
   - Choose rules `c_i` for `g_i` and `c'_i` for `g_i^{-1}`.
2. **Formal cocycles.** For a word `w` in the letters `s_i^{±1}`, composing rules gives a
   local rule `c_w` with `w(g)(x) = c_w(x)·x` on `X`.
3. **The replaced step: triviality.**
   - Suppose `w(g) = id_X`. Then `c_w(x) ∈ Stab(x)` for all `x ∈ X`.
   - For `λ ≠ e`, the set `U_λ = {x ∈ X : c_w(x) = λ}` is clopen and contained in `Fix(λ)`.
     Topological freeness forces `U_λ = ∅`, so `c_w ≡ e` on `X`.
   - In the free case this step was "by freeness".
4. **Invertibility.**
   - Let `Y_2` be the colourings where, at every translate, the formal cocycles of
     `s_i^{-1} s_i` and `s_i s_i^{-1}` are `e`. It is an SFT, and it contains `X` by step 3.
   - On `Y_2`, `T_{c_i}` and `T_{c'_i}` are mutually inverse orbit-preserving homeomorphisms.
5. **Relators.**
   - Fix a finite presentation `<s_1, ..., s_k | r_1, ..., r_m>` with `s_i -> g_i`.
   - Let `Y ⊆ Y_2` add the conditions that every `r_j` has formal cocycle `e` at every
     translate. `Y` is an SFT containing `X`, by step 3.
   - `Y` is invariant under the `hat g_i = T_{c_i}|_Y`, and each `r_j(hat g)` is the identity
     on `Y`.
6. **Isomorphism.**
   - `s_i -> hat g_i|_Y` is a surjection `π : Γ -> Δ_Y`.
   - Restriction to the invariant set `X` is a homomorphism `ρ` with `ρ π = id`.
   - So `π` is an isomorphism. This proves item 1.
7. **Simple case.** The kernel of `Γ -> Homeo(Z)` is normal, so it is trivial or `Γ`. An
   infinite group has only the trivial map onto a finite image, which gives item 2 on finite
   orbits.
8. **Periodic approximations.**
   - Some `g_i` moves some `x`: `c = c_i(x|_D)` with `c·x ≠ x`.
   - (PA), with `W ⊇ D`, `K` the defining shape of `Y`, and `B = {c}`, gives a finite-orbit
     `y` whose `K`-patterns occur in `X`. So `y ∈ Y`.
   - `y|_D = x|_D`, so `hat g_i(y) = c·y`, and `c ∉ Stab(y)` gives `c·y ≠ y`.
   - This contradicts item 2, which proves item 3.
