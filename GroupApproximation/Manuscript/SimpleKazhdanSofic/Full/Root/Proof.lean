import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Elementary
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Ring
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralRingT.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.GeneralTheorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralSimplicity.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofRest
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofSentences
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofIngredients
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.Stepanov
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.Factors
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Converse
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.FlipInvariance
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Generation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Model
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Words
import GroupApproximation.Meta.AxiomGuard

/-!
# Root audit for `simple_kazhdan_sofic_group.tex`: the proofs of `sec:proof` and `sec:main`

Each printed label and subsection of Sections `sec:proof` and `sec:main` is restated as one closed
theorem, a conjunction of the types of the landed `Full` endpoints (`type_of% @Full.SKxx.name`),
proved by the tuple of those endpoints.

* the ingredients (tex l.113–135) and `fig:models` (tex l.137–164);
* `sec:proof` (tex l.218): "The ring and property (T)" with `eq:elementary` (tex l.222–239),
  "Simplicity" (tex l.240–316), "Finite simple models" (tex l.317–343), "Brown's formulation"
  (tex l.344–355);
* `sec:main` (tex l.357): the proof of `thm:main` (tex l.357–392), "Sharpness over `ℤ`"
  (tex l.393–407), "An example" (tex l.408–440).
-/

universe u v

namespace GroupApproximation.Full.SKRoot

/-- **The three ingredients of the proof** (tex l.113–135): property (T), simplicity and finite
models, for every infinite minimal subshift, with the simplicity mechanism over a clopen tower and
both panels of `fig:models` (`SK05.PrintedProofIngredients`), and the per-subshift forms
`SK05.ingredients_propertyT`, `SK05.ingredients_finiteModels`. -/
theorem proof_ingredients :
    type_of% @Full.SK05.printedProofIngredients ∧
    type_of% @Full.SK05.ingredients_propertyT ∧
    type_of% @Full.SK05.ingredients_finiteModels :=
  ⟨@Full.SK05.printedProofIngredients, @Full.SK05.ingredients_propertyT,
    @Full.SK05.ingredients_finiteModels⟩

/-- **`fig:models`** (tex l.137–164): (a) the `5`-periodic sequence `01001` with the words of length
`3` of the Fibonacci subshift, `u ↦ P`, `e_1 ↦ D`; (b) the tower `aV`, `a ∈ B`, and the matrix units
`ε_ab`.  Conjuncts: `SK05.PrintedFigureA`, `SK05.PrintedFigureB`, `SK08.fibonacciDisplay`. -/
theorem fig_models :
    type_of% @Full.SK05.printedFigureA ∧
    type_of% @Full.SK05.printedFigureB ∧
    type_of% @Full.SK08.fibonacciDisplay :=
  ⟨@Full.SK05.printedFigureA, @Full.SK05.printedFigureB, @Full.SK08.fibonacciDisplay⟩

/-- **`eq:elementary`** (tex l.231–234) and the surrounding sentences (tex l.222–239):
`e_ij(r + r') = e_ij(r) e_ij(r')`, `[e_il(r), e_lj(r')] = e_ij(rr')`; the `e_ij(s)`, `s ∈ S`,
generate `EL_n(R)` when `S ∋ 1` generates the ring; and `EL_n` of a finitely generated ring has
property (T) (Ershov–Jaikin-Zapirain).  Conjuncts from `Full.SK03`. -/
theorem eq_elementary :
    type_of% @Full.SK03.printedGeneralElementaryIdentities ∧
    type_of% @Full.SK03.printedGeneralElementaryGeneration ∧
    type_of% @Full.SK03.printedEJZ :=
  ⟨@Full.SK03.printedGeneralElementaryIdentities, @Full.SK03.printedGeneralElementaryGeneration,
    @Full.SK03.printedEJZ⟩

/-- **"The ring and property (T)"** (tex l.222–239): the normal form `∑ f_ξ u_ξ` of
`R = LC(C, F₂) ⋊ Λ` and its multiplication, `e_12(LC(C, F₂))` is infinite, and `EL_n(R)` is an
infinite, finitely generated Kazhdan group.  Conjuncts from `Full.SK03`. -/
theorem proof_ring_T :
    type_of% @Full.SK03.printedGeneralRing ∧
    type_of% @Full.SK03.printedE12Infinite ∧
    type_of% @Full.SK03.printedGeneralPartAWithoutSimplicity ∧
    type_of% @Full.SK03.generalInfiniteFGKazhdan :=
  ⟨@Full.SK03.printedGeneralRing, @Full.SK03.printedE12Infinite,
    @Full.SK03.printedGeneralPartAWithoutSimplicity, @Full.SK03.generalInfiniteFGKazhdan⟩

/-- **"Simplicity"** (tex l.240–316): small clopen sets carry `GL_d(F₂)`, and minimality makes every
nontrivial normal subgroup everything (`SK05.PrintedIngredientsSimplicity`, `SK02.generalSimple`);
and the remark of tex l.307–315, simplicity along Stepanov's Theorem 4.4
(`StepanovMatui.PrintedStepanovTheorem44SimpleRing`, `PrintedSubshiftRingPairDependence`,
`PrintedStepanovRouteSimplicity`, `printedSimplicityStatement_stepanov`). -/
theorem proof_simplicity :
    type_of% @Full.SK05.printedIngredientsSimplicity ∧
    type_of% @Full.SK02.generalSimple.{u, v} ∧
    type_of% @Full.StepanovMatui.printedStepanovTheorem44SimpleRing ∧
    type_of% @Full.StepanovMatui.printedSubshiftRingPairDependence ∧
    type_of% @Full.StepanovMatui.printedStepanovRouteSimplicity ∧
    type_of% @Full.StepanovMatui.printedSimplicityStatement_stepanov :=
  ⟨@Full.SK05.printedIngredientsSimplicity, @Full.SK02.generalSimple.{u, v},
    @Full.StepanovMatui.printedStepanovTheorem44SimpleRing,
    @Full.StepanovMatui.printedSubshiftRingPairDependence,
    @Full.StepanovMatui.printedStepanovRouteSimplicity,
    @Full.StepanovMatui.printedSimplicityStatement_stepanov⟩

/-- **"Finite simple models"** (tex l.317–343): `SL_{nN}(F₂)` is simple, and with maps `φ_k` as in
`thm:general`(b), `EL_n(R)` marked by the `e_ij(s)` is the marked limit of the `SL_{nN_k}(F₂)`, these
form an expander family, and `EL_n(R)` is an expander limit.  Conjuncts from `Full.SK04`. -/
theorem proof_finite_models :
    type_of% @Full.SK04.isSimpleGroup_sl ∧
    type_of% @Full.SK04.thm_general_b_printed :=
  ⟨@Full.SK04.isSimpleGroup_sl, @Full.SK04.thm_general_b_printed⟩

/-- **"Brown's formulation"** (tex l.344–355): a group as in `thm:general`(b) is LEF, sofic and
hyperlinear, `L(G)` is a `II₁` factor embedding in `R^ω`, and `G` lies in the unitary group of the
McDuff factor `L(G) ⊗̄ R`, which embeds in `R^ω`.  Conjuncts: `SK06.brownFormulation_general`, the
factor clauses `SK06.PrintedBrownFactors`, and `SK06.isBrownROmegaForm`. -/
theorem proof_brown_formulation :
    type_of% @Full.SK06.brownFormulation_general ∧
    type_of% @Full.SK06.printedBrownFactors.{u} ∧
    type_of% @Full.SK06.isBrownROmegaForm :=
  ⟨@Full.SK06.brownFormulation_general, @Full.SK06.printedBrownFactors.{u},
    @Full.SK06.isBrownROmegaForm⟩

/-- **`sec:main`, the proof of `thm:main`** (tex l.357–392): an infinite minimal subshift is a
Cantor set on which the shift acts minimally and topologically freely, the ring is generated by
`u^{±1}` and the letter indicators (`SK05.PrintedMainProofOpening`); periodic sequences with the
same words give matricial models, and Theorem `thm:general` applies (`SK05.PrintedMainProofRest`,
`SK05.periodicMatricial`, `SK05.periodicMatricial_printed`). -/
theorem sec_main_proof :
    type_of% @Full.SK05.printedMainProofOpening ∧
    type_of% @Full.SK05.printedMainProofRest ∧
    type_of% @Full.SK05.periodicMatricial ∧
    type_of% @Full.SK05.periodicMatricial_printed :=
  ⟨@Full.SK05.printedMainProofOpening, @Full.SK05.printedMainProofRest,
    @Full.SK05.periodicMatricial, @Full.SK05.periodicMatricial_printed⟩

/-- **"Sharpness over `ℤ`"** (tex l.393–406): for a homeomorphism `T` of a Cantor set `X`,
`EL_3(LC(X, F₂) ⋊_T ℤ)` is simple and Kazhdan if and only if `(X, T)` is conjugate to a minimal
subshift; both directions, the consequence that the subshift hypothesis cannot be dropped, and
invariance under conjugacy and under the flip `T ↦ T⁻¹`.  Conjuncts from `Full.SK07`. -/
theorem sec_main_sharpness :
    type_of% @Full.SK07.simpleKazhdanIffMinimalSubshift ∧
    type_of% @Full.SK07.simpleKazhdan_of_conj_minimalSubshift ∧
    type_of% @Full.SK07.conj_minimalSubshift_of_simpleKazhdan ∧
    type_of% @Full.SK07.subshiftHypothesisCannotBeDropped ∧
    type_of% @Full.SK07.simpleKazhdan_iff_of_conj_or_flip ∧
    type_of% @Full.SK07.simpleKazhdan_iff_symm :=
  ⟨@Full.SK07.simpleKazhdanIffMinimalSubshift, @Full.SK07.simpleKazhdan_of_conj_minimalSubshift,
    @Full.SK07.conj_minimalSubshift_of_simpleKazhdan, @Full.SK07.subshiftHypothesisCannotBeDropped,
    @Full.SK07.simpleKazhdan_iff_of_conj_or_flip, @Full.SK07.simpleKazhdan_iff_symm⟩

/-- **"An example"** (tex l.408–440): the Fibonacci subshift `X_{(3-√5)/2}`, its words of length `3`,
the `5`-periodic sequence `01001`, the model `φ : R_X → M_5(F₂)` with the displayed `P` and `D_1`,
`D_1(e_1) P^3 D_1(e_1) P^{-3} = E_44`, every matrix unit, `φ(S)` generates `M_5(F₂)`, and the
`e_ij(φ(s))` generate `SL_15(F₂)`.  Conjuncts from `Full.SK08`. -/
theorem sec_main_example :
    type_of% @Full.SK08.fibonacciWordsLengthThree ∧
    type_of% @Full.SK08.fibonacciPeriodicWords ∧
    type_of% @Full.SK08.fibonacciModelSetup ∧
    type_of% @Full.SK08.fibonacciWindowsEqual ∧
    type_of% @Full.SK08.fibonacciConjugateE44 ∧
    type_of% @Full.SK08.fibonacciMatrixUnits ∧
    type_of% @Full.SK08.fibonacciModelGeneratesMatrixRing ∧
    type_of% @Full.SK08.fibonacciElementaryGeneration ∧
    type_of% @Full.SK08.fibonacciBlockSpecialLinear ∧
    type_of% @Full.SK08.fibonacciGeneratesMatrices ∧
    type_of% @Full.SK08.fibonacciGeneratesSL15 :=
  ⟨@Full.SK08.fibonacciWordsLengthThree, @Full.SK08.fibonacciPeriodicWords,
    @Full.SK08.fibonacciModelSetup, @Full.SK08.fibonacciWindowsEqual,
    @Full.SK08.fibonacciConjugateE44, @Full.SK08.fibonacciMatrixUnits,
    @Full.SK08.fibonacciModelGeneratesMatrixRing, @Full.SK08.fibonacciElementaryGeneration,
    @Full.SK08.fibonacciBlockSpecialLinear, @Full.SK08.fibonacciGeneratesMatrices,
    @Full.SK08.fibonacciGeneratesSL15⟩

end GroupApproximation.Full.SKRoot

#audit_closed_axioms GroupApproximation.Full.SKRoot.proof_ingredients
#audit_closed_axioms GroupApproximation.Full.SKRoot.fig_models
#audit_closed_axioms GroupApproximation.Full.SKRoot.eq_elementary
#audit_closed_axioms GroupApproximation.Full.SKRoot.proof_ring_T
#audit_closed_axioms GroupApproximation.Full.SKRoot.proof_simplicity
#audit_closed_axioms GroupApproximation.Full.SKRoot.proof_finite_models
#audit_closed_axioms GroupApproximation.Full.SKRoot.proof_brown_formulation
#audit_closed_axioms GroupApproximation.Full.SKRoot.sec_main_proof
#audit_closed_axioms GroupApproximation.Full.SKRoot.sec_main_sharpness
#audit_closed_axioms GroupApproximation.Full.SKRoot.sec_main_example
