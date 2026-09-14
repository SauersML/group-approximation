# skf-consequences — ledger for simple_kazhdan_sofic_group.tex, subsection "Simplicity"

Lane brief: `ct/ROSTER-sk.md` (session nonsofic-existence-49). Target = origin/main tip 9047d0d3c (md5
274f19367f7f706b05c017af721c3884), Simplicity at l.188–253. Rows are keyed by 12-hex sentence hash from
`metadata/SK_SENTENCE_CENSUS.tsv` (regenerated at 9047d0d3c). Every row key below was checked verbatim at the tip.

## History

- The first range, tex 684–743 at b965d63ba (sec:consequences), was removed from the committed note (bf961c128). Nothing was built for it.
- At bf961c128 (tower route through κ₀), I landed `TowerCornerWitness` (TowerStatement, 94f396a4f). The route was rewritten at e80dcf20a, so it is superseded, unwired and has no consumer.
- At e80dcf20a and 9047d0d3c the proof goes through one finite simple subgroup. The note prints EL_3; `thm:main` and ct-two-ended's `PrintedSimplicityStatement` (MainAssembly) cover EL_n for n ≥ 3. So everything here is at Fin n or at a general index type ι.

## Split with ct-bilateral-mf (agreed 19:5x, re-agreed at Fin n)

- ct-bilateral-mf covers l.189–211 and 228–238: small V, the noncommuting root h = e_ij(e_V), k = [g,h] ∈ K∖1, and the entries of k − I and k⁻¹ − I lying in the ε-span. It produces `SimplicityCommutatorWitness T n`.
- skf-consequences covers l.213–226 and 240–252: ε_ab, ψ, H ≤ G, k ∈ H, K ∩ H, H ≅ GL_d(F₂) = PSL_d(F₂) simple, H ⊆ K, e_pq(e_V) ∈ K, J, the cover and K = G.
- The coordinator's 20:15 resume note has ct-bilateral-mf producing k ∈ H_V. The agreed interface is the span witness, and k ∈ H (l.240) is on this side.

CLAIM l.213–226, 240–252 GroupApproximation/Manuscript/SimpleKazhdanSofic/{TowerStatement,TowerMatrixUnits,SimplicityStatement,TowerCopy,TowerCopyGroup,SimplicityNormalSubgroup}.lean

## Carriers

| printed step (tip) | carrier | state |
|---|---|---|
| ε_ab = e_{T^aV}u^{a−b} | `towerE` (TowerStatement) | landed 94f396a4f |
| ε_ab ε_{a′b′} = δ_{ba′}ε_{ab′}; ε_ab ≠ 0 | `towerE_mul_towerE`, `towerE_ne_zero` (TowerMatrixUnits) | landed fb00c31be |
| interface: entries of k − I, k⁻¹ − I in the ε-span | `towerSpanOf`, `SimplicityCommutatorWitness T n` (SimplicityStatement) | landed 23e633ae1 (Fin n) |
| ψ injective, multiplicative, linear | `towerHom`, `towerAddHom_mul`, `towerHom_single`, `towerHom_injective` (TowerCopy) | landed 23e633ae1 |
| M ↦ I − ψ(I_d) + ψ(M) embeds GL_d(F₂) | `flatEquiv`, `towerCopy`, `towerCopy_injective` (TowerCopyGroup) | landed 23e633ae1 |
| H ≤ G: transvections, p ≠ q roots, p = q commutator | `towerCopy_mem_elementaryGroup`, `towerCopy_transvection` | landed 23e633ae1 |
| GL_d(F₂) = SL_d(F₂) = PSL_d(F₂), simple for d ≥ 3 | `det_units_matrix_zmodTwo`, `center_units_matrix_zmodTwo_eq_bot`, `FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo` | landed 23e633ae1 / main |
| k ∈ H via (I + M)(I + M′) = I | `exists_towerCopy_eq`, `mem_range_towerHom_of_mem_towerSpanOf` (SimplicityNormalSubgroup) | probing |
| K ∩ H nontrivial normal, H ⊆ K, e_pq(e_V) ∈ K | inside `eq_top_of_simplicityCommutatorWitness` (codRestrict, comap, simplicity) | probing |
| J two-sided ideal | `Pestov91.SimpleModCentre.levelIdeal` (commutator identities, as printed) | main |
| e_{T^aV} = u^a e_V u^{−a} ∈ J; the finite cover; 1 = 1 − ∏(1 − e_{T^{a_i}V}) ∈ J | `unit_zpow_mul_charFn_mul_inv`, `exists_finset_cover_zpow_image`, `one_sub_map_prod_one_sub_mem`, `prod_one_sub_charFn_eq_zero`, `one_mem_levelIdeal_of_cover` | probing |
| J = R and K = G | `eq_top_of_simplicityCommutatorWitness`; group form `isSimpleGroup_elementaryGroup_of_simplicityCommutatorWitness`; endpoints `printedSimplicityThroughFiniteSimpleSubgroup`, `printedSimplicityIsSimpleGroup` | probing |

The product ∏(1 − e_{T^{a_i}V}) is taken in the commutative ring LC(X, F₂) and pushed through `coeff`, because R_X is not
commutative. The finite cover is proved from compactness and dense orbits (`Pestov91.exists_finset_cover_of_dense_orbits`),
not assumed. For S : Subshift, `minimalSubshift_dense_orbits` gives the dense orbits.

## Open

- Land SimplicityNormalSubgroup, then add the rows for l.240–252 (4931edb04ef5, 71bc505f11f0, 5ca0ef79b43c, 1389f89a7fcc, 6d7586ebf19b, 5e01e0c9f3ac, 01834024ae6c, 52eb27a0e171).
- The sentence rows at l.236 (eb298be3ab50) and l.238 (78f77dd99dc6) are left to ct-bilateral-mf ("lie in it" is its half). Only the clause "say k = I + ψ(M)" is carried here, by `mem_range_towerHom_of_mem_towerSpanOf`.
- cor:lef (lamplighter action of Δ): sk-lef-simplicity will ask for a group-action interface. The level-ideal and cover
  steps are generic. The tower carriers use ℤ exponents, so generalizing them is not cheap.
