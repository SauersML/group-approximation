---
rg: 2
id: banded-matrix-groups-are-subshift-crossed-product-groups
kind: claim
title: Finitely generated groups of banded invertible matrices over a finite field on Z are faithful images of GL_m over crossed products of transitive subshifts
distinct_from:
  bounded-width-subgroups-of-subshift-gl-are-locally-finite: that shows a subgroup of uniformly bounded width is locally finite; this identifies the whole group of banded matrices with banded inverses, and its finitely generated subgroups, with subshift crossed-product groups
artifacts:
  - research/artifacts/sk-exact-banded-2026-09-14-part1.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `F_q` is a finite field and `m ≥ 1`.
- `GL^band(Z×m;F_q)` is the group of invertible `F_q`-linear operators `g` on `F_q^{Z×m}` whose matrices vanish off a band: there is `w` with `g_{(s,i),(t,j)} = 0` whenever `|s−t| > w`, and the same holds for `g^{-1}`.
- `u` is the shift, `uδ_t = δ_{t+1}`.

**Theorem.**
- **(a)** Writing `g = Σ_{|j|≤w} D_j u^j` with `D_j ∈ ℓ^∞(Z, M_m(F_q))` acting diagonally gives
  `GL^band(Z×m;F_q) = GL_m(ℓ^∞(Z,F_q) ⋊ Z) = GL_m(LC(βZ,F_q) ⋊ Z)`,
  the units of the algebraic crossed product by the shift.
- **(b)** Let `Γ ≤ GL^band(Z×m;F_q)` be finitely generated. Then there are:
  - a transitive subshift `Y` over a finite alphabet, with a point `y` whose orbit is dense;
  - a subgroup `Γ̂ ≤ GL_m(LC(Y,F_q) ⋊ Z)`;

  such that the orbit representation `π_y` restricts to an isomorphism `Γ̂ → Γ`.
- **(c)** For every transitive subshift `Y` and every `y` with dense orbit, `π_y` embeds `GL_m(LC(Y,F_q) ⋊ Z)` in `GL^band(Z×m;F_q)`. Regrouping `Z×m` as `Z` gives `GL^band(Z×m;F_q) ≅ GL^band(Z;F_q)`.

**Consequences.**
- For every infinite minimal subshift `X`, `G_X = EL_3(LC(X,F_2) ⋊ Z)` is a subgroup of `GL^band(Z;F_2)`.
- These two statements are equivalent:
  - every finitely generated subgroup of `GL^band(Z;F_q)` is exact;
  - for every transitive subshift `Y` and `m ≥ 1`, every finitely generated subgroup of `GL_m(LC(Y,F_q) ⋊ Z)` is exact.

  Either implies that every `G_X` is exact (open node `subshift-elementary-groups-are-exact`).
- Contrast with permutations: the wobbling group of `Z` has no infinite Kazhdan subgroups (open node, Attempts), but `GL^band(Z;F_2)` contains the infinite simple Kazhdan groups `G_X`.

**Proof:** `banded-matrix-groups-subshift-crossed-product-proof`.
