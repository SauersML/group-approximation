# sk-stepanov: simple_kazhdan_sofic_group.tex l.69–72, the Stepanov route to simplicity

Lane sk-stepanov: a fork launched 2026-09-13 ~20:15 by main (session nonsofic-existence-49; roster `ct/ROSTER-sk.md`, "OA LANES 20:15").
Note at origin e80dcf20a (386 lines, md5 4ad4921253626a4f858866c716a13385); census 09e580c38, row `bf137432ddb7`.

## CLAIM

CLAIM Stepanov Theorem 4.4, simple-ring case GroupApproximation/Algebra/StepanovNormalStructure.lean
CLAIM pair dependence by a dimension count on one cylinder GroupApproximation/Dynamics/ClopenCrossedProductPairDependence.lean
CLAIM printed l.69–72 endpoints GroupApproximation/Manuscript/SimpleKazhdanSofic/StepanovSimplicity.lean

Ownership check, 2026-09-13 20:2x:
- nothing on origin, in the shared tree, in `lanes/*.files` or in landed.log mentions Stepanov, pair dependence or the dimension count;
- ms-intro-3's ledger (row 69–72) lists the cylinder dimension count as its GAP but holds no file for it;
- main's roster assigns l.69–72 to this lane, and ms-intro-3 was told once.

## Ledger (tex l.69–72 at e80dcf20a)

| hash | sentence | carrier | status |
|---|---|---|---|
| `bf137432ddb7` | "Simplicity also follows from Stepanov's theorem on the normal structure of GL_n [Theorem 4.4], since the ring is simple and any two of its elements p,q satisfy pr+qs=0 with (r,s)≠0, by a dimension count on one cylinder." | the ring is simple: `SimpleKazhdanSofic.isSimpleRing` (RingSimpleCentre, landed); pair dependence: new, ClopenCrossedProductPairDependence; Theorem 4.4 for simple rings: new, StepanovNormalStructure; simplicity along this route: new, StepanovSimplicity | in progress |

## Route

1. **Dimension count** (`research/amenable-crossed-products-meet-stepanov-condition-b-proof`, Γ = ℤ).
   - Put the exponents of p and q in S ⊆ [−w, w], and take F = [0, 2w].
   - U is the common fibre, through one point, of the finitely many f_k∘T^m. It is clopen and nonempty; no compactness is needed.
   - r_ρ = Σ_g u^g (ρ_g e_U), and p r_ρ + q r_σ = Σ_m u^m (L(ρ,σ)_m e_U) with L : K^F × K^F → K^[−w,3w].
   - Since 2(2w+1) > 4w+1, L has a nonzero kernel vector. r_ρ = 0 forces ρ = 0 by the uniqueness of Laurent forms.
2. **Condition (b)** at I = 0: α = (0, r, s), b = 1, i = j = 0.
3. **Theorem 4.4** at the generality the sentence uses: R simple, so the only proper ideal is 0 and (a) is vacuous. The conclusion is part (3) of §1.6, with the repo's `relativeElementary` / `congruenceSubgroup` and uniqueness from `PreusserNormalizedBy.eq_of_sandwich`.
   - The proof follows p. 2152: d = c t_{*i}(αλ) c⁻¹ t_{*i}(−αλ).
   - Lemma 4.1 is used only at unit columns: in a subgroup without nontrivial transvections, a zero off-diagonal entry makes the element central, through column transvections.
   - At I = 0, simplicity of R takes the role of Lemma 4.3: β_p ≠ 0 and β_p R c'_{im} = 0 force c'_{im} = 0.
   - The transvection case uses `Pestov91.SimpleModCentre.normal_eq_top_of_elGen_mem` on `PreusserNormalizedBy.elementaryPart`.
4. **Simplicity.** `isSimpleGroup_of_preusser_sandwich` (CongruenceSubgroups) with the sandwich above, Z(R) = F₂ (RingSimpleCentre) and G infinite (ElementaryGroupFacts).

## RESUME 2026-09-13 23:30 (coordinator restart): tip 37551fd93, census 649cb1f80
- The note was restructured at c8b6021ca (one general theorem, thm:general). The Stepanov sentence survives at l.81–85 of 37551fd93, rewritten:
  - ring simplicity now cites [ClarkEdie, Cor. 4.6];
  - the count is "on a tower over one small cylinder".
- New census hash `9424f59fd820`, which supersedes `bf137432ddb7`.
- Printed generality: G_X for an infinite minimal subshift (a ℤ-action), stated right after thm:main, not the Λ-actions of thm:general.

## Modules (in probe)
| module | content |
|---|---|
| `Algebra/StepanovNormalStructure` | Theorem 4.4 over a simple ring. Column transvections in `H` are trivial (`colMatrix_eq_zero_of_mem`), a unit row forces `g = 1` (`eq_one_of_row_eq_one`), Lemma 4.1 at unit columns (`mem_congruenceSubgroup_bot_of_entry_eq_zero`), then the p. 2152 step with `d = [c, t_{*i}(αλ)]` and simplicity in place of Lemma 4.3 (`mem_congruenceSubgroup_bot_of_conditionB`). Also `sandwich_of_conditionB`, `PrintedStepanovTheorem44SimpleRing` and `isSimpleGroup_elementaryGroup_of_conditionB` |
| `Dynamics/ClopenCrossedProductPairDependence` | The tower dimension count for every nonempty `X`, homeomorphism `T` and field `k` (`exists_pair_dependence`, `PrintedPairDependenceClopenCrossedProduct`). Tower `τ_m = u^m e_U`, `0 ≤ m ≤ 2w`; `p τ_m ∈ span{τ_n : -w ≤ n ≤ 3w}`; `2(2w+1) > 4w+1` |
| `Manuscript/SimpleKazhdanSofic/StepanovSimplicity` | Condition (b) from pair dependence (`b = 1`, `α = e_i r + e_j s`), `PrintedSubshiftRingPairDependence`, `PrintedStepanovRouteSimplicity` (ring simple, condition (b), `EL_n` simple for n ≥ 3), `printedSimplicityStatement_stepanov` (discharges MainAssembly's piece) |

Route note: "small" in the section "Simplicity" also asks for disjoint translates. The count uses only the constancy of the coefficients along the tower.

## LANDED 74d702d7a (after the 09-14 reboot): row `9424f59fd820` graded formalized
- Modules, each GREEN in the post-reboot co-probe with BUILT lines:
  - `GroupApproximation/Algebra/StepanovNormalStructure.lean`: `PrintedStepanovTheorem44SimpleRing`, `isSimpleGroup_elementaryGroup_of_conditionB`.
  - `GroupApproximation/Dynamics/ClopenCrossedProductPairDependence.lean`: `PrintedPairDependenceClopenCrossedProduct`, for every nonempty `X`, every homeomorphism and every field.
  - `GroupApproximation/Manuscript/SimpleKazhdanSofic/StepanovSimplicity.lean`:
    - `PrintedSubshiftRingPairDependence`;
    - `PrintedStepanovRouteSimplicity`: the ring is simple, condition (b) holds, and `EL_n(R)` is simple for n ≥ 3;
    - `printedSimplicityStatement_stepanov`: MainAssembly's simplicity piece, discharged by this route.
- Sentence verified verbatim at origin 151ed1151, sha256 `9424f59fd820`.
- The modules are queued for wiring.

## ITEM 2 (main, 09-14 ~08:45): cor:wp's degree representative, split off skf-degrees' item (e)
- Row `7badee43dd9d` (tex l.526–529 at 696c4b602): "Every $S\subseteq\mathbb N$ has the degree of $[0;1+\chi_S(0),1+\chi_S(1),\dots]$, since each digit is decided by one strict comparison with a rational computed from earlier digits."
- Target: `PrintedContinuedFractionRepresentative` in skf-degrees' `WordProblemDegreeStatements`.
- Split proposed to skf-degrees:
  - skf-degrees keeps `ContinuedFractionExpansion` (construction, `IsContinuedFractionOf`, `Irrational`).
  - This lane takes the Turing equivalence and the assembly.

CLAIM alpha computes B (digit k decided by one strict comparison with F_k(1/2), adaptive) GroupApproximation/Manuscript/SimpleKazhdanSofic/ContinuedFractionDigitOracle.lean
CLAIM B computes alpha (rfind over the nested intervals F_n([1/3,3/4])) GroupApproximation/Manuscript/SimpleKazhdanSofic/ContinuedFractionCutOracle.lean
CLAIM assembly of PrintedContinuedFractionRepresentative GroupApproximation/Manuscript/SimpleKazhdanSofic/ContinuedFractionRepresentative.lean

Ownership check 09-14 08:4x: no reduction draft on origin, in the shared tree or in any `.files` (skf-degrees holds only `ContinuedFractionExpansion`, `SturmianComputability`, `SturmianQueries` and `LanguageReducesToWordProblem`).

## LANDED 39e0a0b10: item 2, row `a686ac809830` graded formalized
- The note was shortened at f34e9c0b1 (09:05).
  - The continued-fraction sentence survives with S renamed D: sha256 `a686ac809830`, formerly `7badee43dd9d`.
  - The Stepanov remark was rewritten; row `8cb86180e7d9` now carries it over the landed carriers (2441ef50e; supersedes `9424f59fd820`).
- Split agreed with skf-degrees.
  - skf-degrees: `ContinuedFractionExpansion` (99dc0e949), `ContinuedFractionConvergents` (824bd3166), `OracleRecursion` (aecf7efff).
  - This lane:
    - `ContinuedFractionIntervals` (3bb91638e): the nested intervals and `exists_sep`.
    - `ContinuedFractionDigitOracle`: `charOracle_turingReducible_slopeOracle`, α computes D along the printed route (one strict comparison per digit).
    - `ContinuedFractionCutOracle`: `slopeOracle_turingReducible_charOracle`, D computes α by rfind.
    - `ContinuedFractionRepresentative`: `printedContinuedFractionRepresentative : PrintedContinuedFractionRepresentative`.
- All modules are queued for wiring.

## ITEM 3 (main, 09-14 ~09:25): the word problem of G_Δ = EL₃(LampRing Δ), split off skf-consequences
- Target: `Lamplighter.PrintedLamplighterHostSolvableWordProblem`, tex l.447–455 at 8b36733d7. Rows: `7bfa078c0bed`, `e3cd35e16e2f`, `14148c1b4df0`; all survive in the census regenerated at 8b36733d7.
- Split proposed to skf-consequences (one message): it keeps Λ (row `581584337a04`, `LamplighterAffineWordProblem`); this lane consumes its Λ normal form by name.
- Route:
  - A factor `(d, b, P)` means `1 + x(val d) + b + #{p ∈ P : val p = val d}`, and conjugating by a Λ-word `w` gives `(deltaWord w ++ d, b, P.map (deltaWord w ++ ·) ++ lampPrefixes w)`.
  - Monomials, tables and `matEval`.
  - The coefficient-vanishing criterion over consistent assignments (Ω is the full shift).
  - A truth-table reduction on Δ-word equality queries.

CLAIM syntactic tables and matEval for G_Δ GroupApproximation/Manuscript/SimpleKazhdanSofic/LamplighterHostTables.lean
CLAIM coefficient-vanishing criterion for G_Δ GroupApproximation/Manuscript/SimpleKazhdanSofic/LamplighterHostCriterion.lean
CLAIM truth-table decision and PrintedLamplighterHostSolvableWordProblem GroupApproximation/Manuscript/SimpleKazhdanSofic/LamplighterHostDecision.lean

Ownership check 09-14 09:2x: no host draft on origin, in the shared tree or in any `.files` (skf-consequences holds `LamplighterWordProblem` and `LamplighterAffineWordProblem`).
