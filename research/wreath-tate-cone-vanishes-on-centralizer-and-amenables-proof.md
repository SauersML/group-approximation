---
rg: 2
id: wreath-tate-cone-vanishes-on-centralizer-and-amenables-proof
kind: route
title: Orbit stabilizers of the centralizer on W/H are cyclic, so the inflated Tate object dies there
target: wreath-tate-cone-vanishes-on-centralizer-and-amenables
requires: [tate-diagonal-cone-is-weakly-contractible-wreath-object]
artifacts: [research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part2.md]
---

The full derivation is `research/artifacts/uct-tate-diagonal-wreath-cone-2026-09-13-part2.md`, §5.

- **Finite subgroups and subgroups of `Γ^p`.** These are items of the required claim.
- **Amenable `K`.** Weak contractibility plus Meyer–Nest, arXiv:math/0312292v3, Thm. 8.5.
- **Subgroups of `H`.**
  - `C_0(W/H)` is the `c_0`-sum over `H`-orbits; the fixed orbit contributes `id`.
  - For `wσw^(−1) = cσ` with `c` non-constant, `(δ, …, δ)σ^k` lies in the stabilizer iff
    `δ c_(i−k) δ^(−1) = c_i` for all `i`.
  - The diagonal part of the stabilizer centralizes the nontrivial set `{c_i}`, so it is cyclic.
  - The quotient embeds in `Z/p`.
  - Torsion `(δ)σ^k` with `k ≠ 0` forces `c` constant, which is excluded.
  - So the stabilizer is `Z` or `1`, and `Ind_(K_w)^H Res_(K_w) q^*1_T ≃ 0`.
- **Generation form.** `Ind_K^W(B) ⊗ Y ≅ Ind_K^W(B ⊗ Res_K Y) ≃ 0`, and objects killing `Y` under
  `⊗` form a localizing subcategory.
