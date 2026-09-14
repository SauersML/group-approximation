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

## RESUME 09-14 08:2x: this lane owns all of general Simplicity (sk-lef-simplicity paused and absorbed)

- Evidence for my half. Build log 0914-011028-61503 (MSI) shows `Built` for GeneralTowerUnits, GeneralTowerCopy and GeneralSimplicityNormalSubgroup with no errors. Probe 0914-020044-28236 replayed them green, and the recorded md5s equal the local sources. They are not yet landed: /private/tmp was wiped, and with it the nm infra. Main is rebuilding it, and I hold every probe and landing until main says go.
- Absorbed sk-lef-simplicity drafts: local only, never probed, no attic.
  - `GeneralRootCoefficients`: `commute_elGen_iff`, and coefficient extraction under e_V.
  - `GeneralRoot`: `exists_isSmall_not_commute_elGen`, `PrintedGeneralNonCommutingRoot`.
  - `GeneralCommutatorProducts`: `coeffHom`, `unitHom`, `isCovariantPair`, `mul_charFn_mul_mem`.
  - `GeneralCommutatorSpan`: `epsilonSpan_mul_mem`, `generalCommutatorWitness`, `PrintedGeneralCommutatorWitness`.
  - They sit over `SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ` with an action hypothesis `hact`, and consume the landed `GeneralSmallSets` and my GeneralTowerUnits names; the signatures match.
- New, offline: `GeneralSimplicityAssembly`, which proves ct-two-ended's `PrintedGeneralSimplicityStatement` (local GeneralTheorem). It builds the action from α, minimality, topological freeness and total separation, then applies `generalCommutatorWitness` and `isSimpleGroup_of_generalCommutatorWitness`. The ring spelling is still to confirm with ct-two-ended: its `ActionCrossedProduct α` versus sk-lef-action's landed `ClopenGroupCrossedProduct`.
- The census at 37551fd93 matches the tip 696c4b602 on all 27 Simplicity rows (verbatim check).

## NEW ITEM 09-14 ~09:05: `LEFLamplighterSolvableWordProblemStatement` (LEF groups, tex l.445–455 at 696c4b602)

Taken over from sk-lef-assembly by agreement: the solvable word problem of Λ (words for δ and the lamps of c) and of G_Δ (entries Σ p_ξ u_ξ with polynomial coefficients in finitely many coordinates, checked on all assignments because Ω is the full shift). It is stated over sk-lef-action's `LampRing` and skf-degrees' `wordProblemOracle` / `HasSolvableWordProblem`. The census keys moving here are 581584337a04, 7bfa078c0bed, e3cd35e16e2f and 14148c1b4df0. The heredity key 452e0cc9a605 and "This proves" 6c271814690e stay with sk-lef-assembly.

CLAIM LEF groups l.445–455: solvable word problem of Λ and of G_Δ GroupApproximation/Manuscript/SimpleKazhdanSofic/LamplighterWordProblem.lean

Agreed with sk-lef-assembly (09-14 ~09:10). It drops the four rows at its next landing, and it combines my theorems with sk-lef-action's host theorem into `LEFLamplighterSolvableWordProblemStatement`. l.439–444 (Δ's word problem) belong to sk-lef-ultra (`LEFSecondDelta`).

### Progress (09-14 ~10:10)
- 04544e6d6: statements `PrintedLamplighterAffineSolvableWordProblem` and `PrintedLamplighterHostSolvableWordProblem` (LamplighterWordProblem).
- d80dc37b4: Λ normal form (LamplighterAffineWordProblem): `lampGen`, `deltaWord`, `lampPrefixes`, `lampSum`, `wordValue_lampGen`, `wordValue_lampGen_eq_one_iff`.
- Probing: LamplighterAffineWordProblemReduction, which defines the queries and decision and proves `affineOracle_eq` (Λ's oracle is the decision applied to Δ's answers). It was preserved at ab50d1d6b, and its first probe died in the ~09:36 outage.
- Drafted (attic 6f9c87069): LamplighterAffineWordProblemPrimrec, with `primrec_affineQueries`, `primrec_affineDecide`, `hasSolvableWordProblem_lampAffine` and the closed `printedLamplighterAffineSolvableWordProblem`.
- G_Δ split agreed with sk-stepanov (09:3x). sk-stepanov takes `PrintedLamplighterHostSolvableWordProblem` and rows 7bfa078c0bed, e3cd35e16e2f and 14148c1b4df0, consuming my Λ normal form by name. This lane keeps Λ and row 581584337a04 (drafted locally; it lands after the carriers).
- sk-lef-assembly has dropped all four rows (checked on origin). l.439–444 belong to sk-lef-ultra.
- Simplicity rows re-keyed at fee2f017e (f9d00128c766→18ac299bc474, fd2fdac50185→e503326bf5e2, db6d6604b3d3→5b3ad392ecb5, 18455b63420b→2b5ba855ed5c).

### Statements (landed): `LamplighterWordProblem`
- `Lamplighter.PrintedLamplighterAffineSolvableWordProblem`: `HasSolvableWordProblem Δ → HasSolvableWordProblem (LampAffine Δ)` (l.445–447).
- `Lamplighter.PrintedLamplighterHostSolvableWordProblem`: `HasSolvableWordProblem Δ → HasSolvableWordProblem ↥(elementaryGroup (Fin 3) (LampRing Δ))` (l.448–455).

### Gap report and route

Nothing on origin decides a word problem relative to another group's word problem, apart from translation between generating sets. The route reuses:
- `Computability/OracleTruthTable.turingReducible_of_truthTable`: primrec queries plus a primrec decision on the answers;
- `partrec_iff_forall_turingReducible` (as in `printedSolvableWordProblemHeredity`);
- ms-traces-3's pattern (`WordNormalForm`, `WordTablePrimrec`, `WordProblemDecision`).

**Λ (l.445–447)**, est. ~400 lines, module `LamplighterAffineWordProblem`.
1. Letters are `Option ι`: `none ↦ z` and `some i ↦ inr (t i)`.
2. Semantics: `wordValue` of w is `(Σ_k 1_{value p_k}, value (deltaWord w))`, where the p_k are the Δ-prefixes before the z letters. This follows by induction, from `z⁻¹ = z` and `inr δ · inl F = inl (δ·F) · inr δ`.
3. Triviality ⇔ `deltaWord w` is trivial and every position occurs an even number of times. So the queries are `deltaWord w` and all `p_j⁻¹ p_k`, and the decision is parity counting.
4. Primrec of the queries and the decision: list_flatMap/list_map/list_range combinators.

**G_Δ (l.448–455)**, est. ~1500 lines over 5–6 modules.
1. Syntactic tables. An entry is a list of monomials (Λ-word ξ, list of (Δ-word δ, shift bit)), for coefficient products `Π (x(δ) + 1 + c(δ))` from `u_ξ e_U u_ξ⁻¹ = 1_{x(δ) = 1 + c(δ)}`.
2. `matEval` into `LampRing Δ`, by multiplication rules in `ClopenGroupCrossedProduct`. The letters are `e_ij(s)` with s ∈ {1, u_{z}, u_{t_i}^±, e_U}.
3. Criterion: `M = I₃` iff every coefficient polynomial of M − I₃ vanishes on all assignments. It uses:
   - injectivity of the coefficient map;
   - Ω being the full shift `Δ → ZMod 2`, so a polynomial function in finitely many distinct coordinates is zero iff it vanishes at every assignment;
   - collecting equal ξ and equal coordinates through Δ-word equality queries.
4. Truth-table reduction:
   - queries: all pairwise comparisons among the finitely many Δ-words in the tables, plus Λ-equality via the Λ reduction;
   - decision: partition coordinates, collect coefficients, evaluate every assignment, all primrec.

## NEW ITEM 09-14 ~08:55: simplicity half of `LEFLamplighterStatement` (cor:lef, cor:host)

The host G_Δ = EL₃(LC(Z,F₂) ⋊ L) must be simple, through the general theorem (`General.isSimpleGroup_clopenGroupCrossedProduct`). This lane takes the simplicity half:
- the lamplighter action of L on Z = F₂^Δ is minimal;
- it is topologically free, and every nonempty clopen set contains a small one (general `exists_isSmall_subset`);
- EL_n of the lamplighter crossed product is simple for n ≥ 3.

sk-lef-action keeps the crossed product, the generation and the finite models.

CLAIM LEF section, proof of cor:lef/cor:host: lamplighter minimality, topological freeness, simplicity of G_Δ GroupApproximation/Manuscript/SimpleKazhdanSofic/LamplighterSimplicity.lean

Split sent to sk-lef-action (one message, 09-14 ~08:56). It keeps the crossed product, LamplighterAction (`isMinimal` and `isTopologicallyFree` were already landed at 407f74f33), LamplighterRing, the finite models, and the host's other IsLEFHost clauses.

- 31f62584d: LamplighterSimplicity (BUILT, probe 0914-085834-30680), queued for wiring. It proves `Lamplighter.isSimpleGroup_lampRing`: EL_n(LampRing Δ) is simple for infinite Δ and n ≥ 3, by `General.isSimpleGroup_clopenGroupCrossedProduct` with `isMinimal`, `isTopologicallyFree`, and Mathlib's instances on Δ → ZMod 2. The closed endpoint is `printedLamplighterHostSimple`.
- Census row 358e51e6a815 (l.419, the simplicity clause of "By Theorem thm:general, G_Δ … is … simple"), status partial: the other clauses are sk-lef-action's.

## INFRA READY 09-14 (new NM at this session's scratchpad; clone ring-b-end)

- Main's rulings:
  - A cache-replay GREEN is acceptable for GeneralTowerUnits, GeneralTowerCopy and GeneralSimplicityNormalSubgroup, because MSI build log 0914-011028-61503 shows all three `Built`, errors=0, sorry=0, "Build completed successfully". Their sources are unchanged since 00:47 (md5 3ae948aa / 17c2df24 / bfbc37a8).
  - The crossed product is sk-lef-action's landed `ClopenGroupCrossedProduct Λ Z k`, and ct-two-ended adapts GeneralTheorem to it.
- Retargeted assembly: `General.isSimpleGroup_clopenGroupCrossedProduct` and `PrintedGeneralSimplicityClopenGroup` over `[MulAction Λ Z] [ContinuousConstSMul Λ Z] [CompactSpace Z] [TotallySeparatedSpace Z] [Nonempty Z] [MulAction.IsMinimal Λ Z]`, with topological freeness as `interior {z | ξ • z = z} = ∅`.
- Preserved all eight General drafts (attic 1907a02ee). The co-probe of all eight is running.

### Absorbed first half (sk-lef-simplicity), carriers

| printed step (tip) | carrier | module |
|---|---|---|
| 1 ≠ g ∈ K, bound w, B_w, B_{2w} (l.152) | construction inside `generalCommutatorWitness` | GeneralCommutatorSpan |
| V small (l.154) | `IsSmall` | GeneralSmallSets (landed) |
| moved points dense; small subsets (l.157) | `isClosed_fixed`, `dense_moved`, `exists_isSmall_subset` | GeneralSmallSets (landed) |
| some h = e_ij(e_V) does not commute with g (l.161–172) | `commute_elGen_iff`, `coeff_mul_charFn_apply`, `coeff_charFn_mul_apply`, `exists_forall_coeff_*_ne_zero`, `offDiag_eq_zero`, `coeff_diag_eq_zero`, `coeff_one_diag_eq`, `eq_one_of_commute_elGen_small`, `exists_isSmall_not_commute_elGen` | GeneralRootCoefficients, GeneralRoot |
| k = [g,h] ∈ K∖1 (l.188) | `generalCommutatorWitness` (hkK, hk1) | GeneralCommutatorSpan |
| display fu_a e_V f′u_b ∈ {0, ε_{a,b⁻¹}} (l.190–194) | `single_mul_charFn_mul_single_mem` | GeneralCommutatorProducts |
| entries of k − I, k⁻¹ − I in M_n(A_V) (l.194–196) | `mul_charFn_mul_mem`, `epsilonSpan_mul_mem`, `generalCommutatorWitness` | GeneralCommutatorProducts, GeneralCommutatorSpan |
| covariant pair for `SkewMonoidAlgebra (LC(Z,F₂)) Λ` | `coeffHom`, `unitHom`, `smul_charFn`, `isCovariantPair` | GeneralCommutatorProducts |

Census rows for all 27 Simplicity keys are drafted in `metadata/sk-census-rows/skf-consequences.tsv`. They land after the modules they name. The census was regenerated at 696c4b602 (aa6f988f4), and all 27 keys are verbatim at the tip.

### Landing log (09-14)

- ead0eb94e: GeneralTowerUnits, GeneralTowerCopy, GeneralSimplicityNormalSubgroup (queued for wiring), on cache-replay evidence confirmed by MSI build log 0914-011028-61503.
- 36821ec19: GeneralRootCoefficients (BUILT, probe 0914-083727-91673), after two `omit [MulAction Λ Z] in` fixes.
- Fixes to the absorbed drafts, before the re-probe:
  - GeneralRoot: the deprecated `coeff_one_one` becomes `coeff_one` plus `Finsupp.single_eq_same`.
  - GeneralCommutatorProducts: the `1 x = 1 z` goal in `smul_charFn` closes by `simp only [.., Pi.one_apply]`.
  - GeneralCommutatorProducts: in `charFn_mem_epsilonSpan`, `one_smul` becomes `smul_one`, since the motive broke on `1 • V` inside the charFn proof.
- 95c3ebda0: GeneralRoot and GeneralCommutatorProducts (BUILT, probe 0914-084317-69202).
- GeneralCommutatorSpan: `open scoped commutatorElement`, for the `⁅g, h⁆` notation (a missing `Bracket` instance).
- 69643f441: GeneralCommutatorSpan (BUILT, probe 0914-084649-79491), after the `k − I`, `k⁻¹ − I` identities were rewritten with explicit `add_mul`/`mul_sub` steps plus `abel` (`noncomm_ring` left `-1 •` terms).
- 9e63c6916: census rows for all 27 Simplicity keys (census aa6f988f4 at 696c4b602), carriers verified on origin (54 names).
- 81ae4081d: GeneralSimplicityAssembly (BUILT, probe 0914-084834-66611), queued for wiring. **Closed endpoint**: `General.printedGeneralSimplicityClopenGroup`.
- GeneralSimplicityAssembly adds `isSimpleGroup_clopenGroupCrossedProduct_of_isOpen` with ct-two-ended's printed hypotheses:
  - `MulAction.IsMinimal`;
  - "no nontrivial element fixes a nonempty open set" (`IsTopologicallyFreeAction`);
  - compact, metrizable, totally disconnected, nonempty.

  ct-two-ended discharges `PrintedGeneralSimplicityStatement` in its own `GeneralTheoremClosure`.

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
