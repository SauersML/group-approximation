# skf-consequences: ledger for simple_kazhdan_sofic_group.tex, subsection "Simplicity"

Lane brief: `ct/ROSTER-sk.md` (session nonsofic-existence-49). Target is the origin/main tip 37551fd93 (restructured at
c8b6021ca around `thm:general`). Simplicity is at l.151–210 and is proved for a finitely generated group Λ acting minimally
and topologically freely on a Cantor set Z, with R = LC(Z, F₂) ⋊ Λ and EL_n(R) for n ≥ 3. Rows are keyed by 12-hex sentence
hash from `metadata/SK_SENTENCE_CENSUS.tsv`, which is regenerated at 37551fd93.

## History

- b965d63ba: tex 684–743 (sec:consequences) was removed from the committed note, so nothing was built for it.
- bf961c128: I built the tower route through κ₀ (`TowerCornerWitness`, TowerStatement 94f396a4f). It was superseded at e80dcf20a.
- e80dcf20a to 9047d0d3c: the ℤ route through one finite simple subgroup, printed for EL_3 and built at Fin n. Landed:
  - TowerMatrixUnits fb00c31be;
  - SimplicityStatement, TowerCopy and TowerCopyGroup 23e633ae1;
  - SimplicityNormalSubgroup 03e9b778b, with `isSimpleGroup_elementaryGroup_of_simplicityCommutatorWitness` and `printedSimplicityIsSimpleGroup`.

  These carriers stay valid Lean. At the tip no printed sentence names them, because thm:main now follows from thm:general.
- 23:15 restart: ct-bilateral-mf was not resumed, and this lane absorbs its Simplicity drafts and report:
  - landed: TowerRootDetection, SimplicityNonCommutingRoot;
  - attic 525d38a75, unlanded: SimplicitySmallSets, SimplicityCommutationCriterion, SimplicitySmallRoot.

  They are ℤ-specific and cover the first half of the proof. That half now belongs to sk-lef-simplicity at Λ generality (below), which is free to mine them. `commute_elGen_iff` in SimplicityCommutationCriterion is index-free.

## Split with sk-lef-simplicity (agreed 09-14 ~00:15)

One proof at Λ generality, n ≥ 3.
- sk-lef-simplicity takes l.151–172 and 188–196: w, small V, topological freeness ⇒ small subsets, the noncommuting root h = e_ij(e_V), k = [g,h], fu_a e_V f′u_b ∈ {0, ε_{a,b⁻¹}}, and k − I, k⁻¹ − I in M_n(A_V). It produces `GeneralCommutatorWitness` for the concrete pair R = SkewMonoidAlgebra (LC(Z, F₂)) Λ, coeff = single 1, u ξ = single ξ 1.
- skf-consequences takes l.176–186 and 197–208: ε_ab, the δ rule, A_V ≅ M_B(F₂), the embedding of GL_n(A_V), H_V ≤ G, k ∈ H_V, K ∩ H_V simple, H_V ⊆ K, e_pq(e_V) ∈ K, J, e_{ξV} ∈ J, the cover, K = G, and IsSimpleGroup.
- Interface: `GeneralSimplicityStatement`. It is stated over an abstract covariant pair (an injective coeff : LC(Z, F₂) →+* R, units u : Λ →* Rˣ, and u_ξ e_U = e_{ξU} u_ξ), so it does not wait on a concrete crossed product.

CLAIM l.176–186, 197–208 GroupApproximation/Manuscript/SimpleKazhdanSofic/{GeneralSimplicityStatement,GeneralTowerUnits,GeneralTowerCopy,GeneralSimplicityNormalSubgroup}.lean

## Carriers at the tip (probing 0914-00xx)

| printed step (37551fd93) | carrier | state |
|---|---|---|
| e_{ξU} = u_ξ e_U u_ξ⁻¹ (ring section, as used here) | `IsCovariantPair.covariance`, `General.unit_mul_charFn_mul_inv` | probing |
| d = 3\|B_w\|; ε_ab = e_{aV}u_{ab⁻¹} (l.176) | `epsilon`; d = card (Fin n × B) | probing |
| ε_ab ε_a′b′ = δ_{ba′} ε_ab′ (l.177) | `General.epsilon_mul_epsilon` (TranslatesDisjoint B V) | probing |
| V ≠ ∅, A_V ≅ M_B(F₂) with unit e; y ↦ (1−e)I + y embeds GL_n(A_V) (l.180) | `epsilon_ne_zero`, `epsilonHom`, `epsilonHom_single`, `epsilonHom_injective`, `blockFlatEquiv`, `copyGL`, `copyGL_injective` | probing |
| H_V ≤ G: transvections e_pq(ε_ab), p ≠ q, and commutators (l.183) | `copyGL_transvection`, `copyGL_mem_elementaryGroup`, `FinitaryLinear.elementaryGroup_zmodTwo_eq_top`, `elementaryUnit_commutator` | probing |
| y y′ = y′ y = eI, so k ∈ H_V (l.197) | `exists_copyGL_eq` via `ChainRadical.exists_cornerUnitHom_eq` | probing |
| K ∩ H_V nontrivial normal in GL_d(F₂) = PSL_d(F₂), simple, so H_V ⊆ K and e_pq(e_V) ∈ K (l.199) | inside `eq_top_of_generalCommutatorWitness`; `FinitaryLinear.isSimpleGroup_units_matrix_zmodTwo`; `det_units_matrix_zmodTwo`, `center_units_matrix_zmodTwo_eq_bot` (23e633ae1) | probing |
| J two-sided ideal (l.203) | `Pestov91.SimpleModCentre.levelIdeal` (the printed commutator identities) | main |
| e_{ξV} ∈ J (l.206) | `one_mem_levelIdeal_of_smul_cover` (htrans) | probing |
| minimality and compactness give a finite cover; 1 = 1 − ∏(1 − e_{ξᵢV}) ∈ J (l.207) | `exists_finset_smul_cover`, `prod_one_sub_charFn_smul_eq_zero`, `one_sub_map_prod_one_sub_mem` | probing |
| J = R and K = G (l.208) | `eq_top_of_generalCommutatorWitness`, `isSimpleGroup_of_generalCommutatorWitness`, `printedGeneralSimplicityFromWitness` | probing |

The product ∏(1 − e_{ξᵢV}) is taken in the commutative ring LC(Z, F₂) and pushed through `coeff`. The finite cover is proved
from `[CompactSpace Z] [MulAction.IsMinimal Λ Z]` (`IsOpen.iUnion_smul`), not assumed.

## Census

The ℤ-era row keys in `metadata/sk-census-rows/skf-consequences.tsv` (keyed at 9047d0d3c) are no longer in the census at
37551fd93. Once the General modules land, I replace them with rows for 2e100de03692, 96d063dce333, 5ce2f653f637, f9d00128c766,
16fd7b95d922, 18455b63420b, ebd3562205bb, 2cfda59ab817, 8269b12fdd2c, 5a6ac852aa57 and 46368870a699.
