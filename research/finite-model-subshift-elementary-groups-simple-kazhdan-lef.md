---
rg: 2
id: finite-model-subshift-elementary-groups-simple-kazhdan-lef
kind: claim
title: For a free minimal subshift with finite models over a finitely generated group, EL_n over the binary crossed product is infinite simple Kazhdan and LEF, by clopen towers
distinct_from:
  residually-finite-group-toeplitz-elementary-groups-lef-kazhdan: that is one binary Toeplitz subshift per residually finite group, proved through Steinberg simplicity and matricial embeddings; this is every free minimal subshift with finite models, proved by the elementary tower argument of the manuscript, and it needs freeness at every point.
  residually-finite-actions-give-matricial-crossed-products: that gives the matricial embedding and LEF for topologically free residually finite actions over any field; this adds simplicity of EL_n over F_2 by clopen towers and states the manuscript-facing theorem.
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that is Z^d with rank models and linear soficity; this is any finitely generated acting group under the finite-model hypothesis, with LEF.
artifacts:
  - research/artifacts/sk-general-actions-a-finite-subshift-limits-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a finitely generated group acting on `A^Γ` by `(γx)(h) = x(hγ)`, and `X ⊆ A^Γ` an infinite minimal subshift on which `Γ` acts freely. Suppose `X` has finite models: for every finite `F ⊆ Γ` some finite invariant `Y ⊆ A^Γ` has `{y|_F : y ∈ Y} = {x|_F : x ∈ X}`. Let `R = LC(X,F_2) ⋊ Γ` and `n ≥ 3`. Then `EL_n(R)` is an infinite, finitely generated, simple group with property (T) that is LEF, hence sofic and hyperlinear.

**Proof** (artifact §1). This is the proof of the manuscript `simple_kazhdan_sofic_group.tex`, with `u^j` replaced by `u_γ` and exponent bounds by word length.
- (T) comes from EJZ.
- `R` is simple with `Z(R) = F_2` (freeness and minimality), so `Z(EL_n(R)) = 1`.
- LEF: evaluate coefficients on a finite subshift `Y` with the patterns of `X` on a large window. Compactness and freeness make the relevant nontrivial elements act on `Y` without fixed points, so nonzero elements stay nonzero.
- Simplicity: commute `g ∈ N` with `e_ij(e_C)` or `e_ij(e_C u_t)` for a clopen partition with `C ∩ γC = ∅`, `γ ∈ B_(2w+2) \ {e}`. The commutator lands in `LC(C, GL_d(F_2))`, `d = n|B_(w+1)|`. A constant non-identity value on `W` gives `H_W ≅ GL_d(F_2) ⊆ N`, then `e_12(e_W) ∈ N`, and the level ideal is `R`.

**Scope.**
- `Γ = Z`: every infinite minimal subshift qualifies (return words), giving `infinite-simple-kazhdan-hyperlinear-group`.
- By `free-subshift-with-finite-models-forces-rf-group` only residually finite `Γ` admit such `X`, and by `rf-groups-have-free-minimal-subshifts-with-finite-models` every infinite finitely generated residually finite `Γ` does.
- Topological freeness is not enough for the tower partition; for that case use `steinberg-elementary-groups-are-simple-mod-centre`.

Route: `finite-model-subshift-elementary-groups-simple-kazhdan-lef-proof`.
