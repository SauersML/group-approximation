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

**ESTABLISHED (sk-verify-18 PASS, wording fixes W1–W2 merged).**

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
- Contrast with permutations: the wobbling group of `Z` has no infinite countable property (T) subgroup, but `GL^band(Z;F_2)` contains the infinite simple Kazhdan groups `G_X`. The first fact is Juschenko–de la Salle, *Invariant means for the wobbling group*, arXiv:1301.4736, Theorem 4.1, for `W(Y)` with `Y` of uniform subexponential growth, which `Z` has; it is quoted on main in `elek-monod-near-hit-has-torsion-no-kazhdan-subgroup-proof`.

**Proof:** `banded-matrix-groups-subshift-crossed-product-proof`.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part11.md`):** re-derived (a) the banded operators as the algebraic crossed product, with ℓ^∞(Z,F_q) = LC(βZ,F_q); (b) coding the coefficient functions as a point, faithfulness of π_y on a dense orbit, lifted inverses; (c) and the consequences. Wording W1: the m = 1 model test I + δ_0 is singular over F_2, so use a coordinate swap at site 0 with m = 2. W2: the wobbling-group contrast is a theorem, Juschenko–de la Salle arXiv:1301.4736 Theorem 4.1, as quoted on main in `elek-monod-near-hit-has-torsion-no-kazhdan-subgroup-proof`; cite it rather than the open node. Both merged (sk-cairn-steward-5, 2026-09-14).
