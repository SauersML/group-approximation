# Lane ct-bilateral-mf: simple_kazhdan_sofic_group.tex, subsection "Simplicity"

Target: the CURRENT origin/main tip of the note (ROSTER-sk protocol 19:45). At e80dcf20a (386 lines, md5
4ad4921253626a4f858866c716a13385) the subsection "Simplicity" is tex ≈179–238. Rows are keyed by the 12-hex sentence hash
of `metadata/SK_SENTENCE_CENSUS.tsv`, once skf-census regenerates the census at the tip. On origin it is still at bf961c128.

History:
- b965d63ba l.574–683 (thm:root, cor:simple);
- bf961c128 l.174–204 (tower detection);
- e80dcf20a Simplicity. The tower route (B_m(U), κ, W) was removed from the note, so earlier carriers are superseded.

## Split (agreed with skf-consequences, 09-13 ~19:50)

- ct-bilateral-mf: l.180–196 and 210–221. The bound w; small V; no periodic points; small neighbourhoods; finite disjoint
  unions; some h = e_ij(e_V), V small, not commuting with g; k = [g,h] ∈ N∖{1}; fu^a e_V f′u^b ∈ {0, ε_{a,−b}}; the entries
  of ghg⁻¹ − I₃; h⁻¹ = h; k − I₃ = (ghg⁻¹ − h)h and k⁻¹ − I₃ = h(ghg⁻¹ − h) in the ε-span.
- skf-consequences: l.197–209 and 222–238. ε_ab nonzero and products; ψ; the embedding of GL_d(F₂) and H ≤ G; k ∈ H;
  simplicity of GL_d(F₂) = PSL_d(F₂); H ≤ N; the ideal J; N = G.
- Interface: `SimplicityCommutatorWitness T` (skf-consequences, module `Manuscript/SimpleKazhdanSofic/SimplicityStatement`). For
  N ⊴ EL₃(R_X), N ≠ ⊥: a nonempty clopen V with `LevelsDisjoint T w V`, and k ∈ N, k ≠ 1, with the entries of k − 1 and
  k⁻¹ − 1 in `towerSpanOf T (ZMod 2) w hV` (ε_ab = `towerE T (ZMod 2) w hV a b`). I produce it.

## Route verdict

The printed route: a small set V, a non-commuting e_ij(e_V) via the scalar argument, the finite copy of GL_d(F₂), k ∈ H.
It is not the route of Pestov91 `SplitSimplicity` or `SimpleModCentre`.

Reusable carriers:
- ct-involution `Manuscript/SimpleKazhdanSofic/RingPartitions` (2f481625d): `IsMinimalSystem`, `zpow_apply_ne_self` (no
  periodic points, tex 185), `exists_clopen_nbhd_disjoint_translates`, `exists_clopen_partition_disjoint_translates`, `eU`.
- Pestov91 `SimpleModCentre.commutingSubring` (the coefficients commuting with g are additive).
- Mathlib `Matrix.mem_range_scalar_of_commute_single` (a matrix commuting with all E_ij is scalar).

## Sentence ledger (tex lines at e80dcf20a; hashes pending the census)

| l. | sentence (abridged) | carrier | status |
|---|---|---|---|
| 180 | let 1 ≠ N ⊴ G and 1 ≠ g ∈ N | binder of the producer | structural |
| 180–181 | w ≥ 0 bounds the exponents of the entries of g, g⁻¹ | `SimpleKazhdanSofic.exists_matrix_exponent_bound` (TowerRootDetection, probing) | open |
| 182–184 | V small: V ∩ T^jV = ∅ for 0<\|j\|≤2w and every f∘T^i (\|i\|≤w, f a coefficient of an entry of g, g⁻¹) constant on V | to build, SimplicitySmallSets | definition |
| 185–186 | no periodic points, so every point has a small clopen neighbourhood | `RingPartitions.zpow_apply_ne_self`, `exists_clopen_nbhd_disjoint_translates`; the constancy clause to build | open |
| 186–187 | every clopen set is a finite disjoint union of small ones | to build (compactness), SimplicitySmallSets | open |
| 189 | some h = e_ij(e_V) with V small does not commute with g | to build, SimplicityNonCommutingRoot | open |
| 190–191 | otherwise g commutes with e_ij(e_V) for every clopen V, by eq:elementary | `commutingSubring` additivity plus the disjoint union | open |
| 191 | V = X gives g = cI₃, c = Σ c_j u^j | `Matrix.mem_range_scalar_of_commute_single` | open |
| 192–194 | e_V c − c e_V = Σ c_j (e_V − e_{T^jV}) u^j vanishes; separating z from T^{−j}z gives c_j = 0, j ≠ 0 | to build (indicator-only form of the argument in ct-involution's `mem_center_iff`) | open |
| 195–196 | c ∈ LC(X,F₂), and cc⁻¹ = 1 gives c = 1 and g = 1 | to build | open |
| 213 | k = [g,h] ∈ N ∖ {1} | `SimpleKazhdanSofic.commutatorElement_mem_ne_one` (TowerRootDetection, probing) | open |
| 214–219 | fu^a e_V f′u^b = f e_{T^aV}(f′∘T^{−a})u^{a+b} ∈ {0, ε_{a,−b}} | to build, SimplicityCommutatorSpan | open |
| 219–221 | the entries of ghg⁻¹ − I₃ = g e_V E_ij g⁻¹ are sums of such products; h⁻¹ = h = I₃ + ε_00 E_ij | to build | open |
| 223–224 | k − I₃ = (ghg⁻¹ − h)h, k⁻¹ − I₃ = h(ghg⁻¹ − h) lie in the ε-span | to build (span closed under products: skf-consequences' products); produces `SimplicityCommutatorWitness` | open |

## Modules (claimed)

- CLAIM l.180–181, 213 GroupApproximation/Manuscript/SimpleKazhdanSofic/TowerRootDetection.lean (trimmed to the tip)
- CLAIM l.182–187 GroupApproximation/Manuscript/SimpleKazhdanSofic/SimplicitySmallSets.lean
- CLAIM l.189–196 GroupApproximation/Manuscript/SimpleKazhdanSofic/SimplicityNonCommutingRoot.lean
- CLAIM l.213–224 GroupApproximation/Manuscript/SimpleKazhdanSofic/SimplicityCommutatorSpan.lean
- Withdrawn, never landed: TowerPartitionGenerators (the bf961c128 generators route), TowerCornerLocalization.

## Progress log

- 09-13 19:1x: ledger at bf961c128 (7bfa51cf8).
- 09-13 19:5x: re-keyed to the tip e80dcf20a; split re-agreed; TowerRootDetection trimmed and re-probing.
