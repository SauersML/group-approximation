import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofSentences
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.ProofRest
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.Expanders
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FreeAlgebraKazhdan
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialQuotientsExpanders
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitTransport
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainFromGeneral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralSimplicity.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Model
import GroupApproximation.Meta.AxiomGuard

/-!
# The three ingredients of the proof (I1) and `fig:models`

`simple_kazhdan_sofic_group.tex`, tex l.113–135 ("The proof has three ingredients") and the caption
of Figure `fig:models` (tex l.159–163).

* **Property (T)** (tex l.114–119): `IngredientsPropertyT`. Every element of
  `LC(X, F₂) ⋊_T ℤ` is a finite sum `∑_j f_j u^j`, `u f u⁻¹ = f ∘ T⁻¹`, the ring is finitely
  generated, and `G_X` has property (T).
* **Simplicity** (tex l.120–124): `PrintedIngredientsSimplicity`, in the general setting of
  `thm:general` (a) (Steps 2–3 of `Full.SK02`): `GL_d(F₂)` is simple for `d ≥ 3`; a nontrivial normal
  subgroup contains a nontrivial element of `M_n(A_V)` over a clopen tower; the tower gives an
  injective copy `GL_{n×B}(F₂) → EL_n(R)` sending transvections to elementary matrices `e_pq(ε_ab)`;
  a normal subgroup meeting the copy nontrivially contains the whole copy; and every nontrivial
  normal subgroup is everything. For `G_X` itself, simplicity is the second conjunct of
  `PrintedProofIngredients`.
* **Finite models** (tex l.125–135): `IngredientsFiniteModels`. Periodic sequences with the words of
  `X`; the shift becomes the cyclic permutation matrix and letter indicators become diagonal matrices
  (`ProofRestModels`); marked limit of `SL_{3N}(F₂)` with expanding Cayley graphs; the `SL_{3N}(F₂)`
  are quotients of the Kazhdan group `EL₃(F₂⟨S⟩)`; and `G_X` is an expander limit (printed sense).
  The citation of Grigorchuk–Medynets (tex l.128–129) is only a comparison and is not used.
* **Figure (a)** (tex l.159–161): `PrintedFigureA`, from `Full.SK08`.
* **Figure (b)** (tex l.161–162): `PrintedFigureB`: `(ab⁻¹)(bV) = aV`, `ε_ab = e_{aV} u_{ab⁻¹}`, and
  the `ε_ab` multiply as matrix units.

All statements are closed and proved from corpus theorems, with no literature hypothesis.
-/

namespace GroupApproximation.Full.SK05

open GroupApproximation.SimpleKazhdanSofic
open GroupApproximation.ClopenCrossedProduct
open GroupApproximation.WordGraph
open SymbolicDynamics.FullShift
open scoped Pointwise

/-! ## Ingredients for a subshift -/

section Subshift

variable {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] [Finite A]

/-- **Ingredient: property (T)** (tex l.114–119): the Laurent form `∑_j f_j u^j`, the covariance
`u f u⁻¹ = f ∘ T⁻¹`, finite generation of the ring, and property (T) of `G_X`. -/
abbrev IngredientsPropertyT (S : Subshift A ℤ) : Prop :=
  (∀ r : R S, ∃ (J : Finset ℤ) (f : ℤ → LocallyConstant S.carrier (ZMod 2)),
    r = ∑ j ∈ J, coeff (subshiftHomeo S) (ZMod 2) (f j) *
      ((unit (subshiftHomeo S) (ZMod 2) ^ j : (R S)ˣ) : R S)) ∧
  (∀ f : LocallyConstant S.carrier (ZMod 2),
    (unit (subshiftHomeo S) (ZMod 2) : R S) * coeff (subshiftHomeo S) (ZMod 2) f *
        (((unit (subshiftHomeo S) (ZMod 2))⁻¹ : (R S)ˣ) : R S) =
      coeff (subshiftHomeo S) (ZMod 2)
        (LocallyConstant.comap ⟨⇑(subshiftHomeo S).symm, (subshiftHomeo S).symm.continuous⟩ f)) ∧
  IsFinitelyGeneratedRing (R S) ∧ HasKazhdanPropertyT.{0, 0} (G S)

theorem ingredients_propertyT (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : IsMinimal S) :
    IngredientsPropertyT S :=
  ⟨fun r => ClopenCrossedProduct.exists_sum_coeff_mul_unit_zpow (subshiftHomeo S) (ZMod 2) r,
    covariance S, ⟨printedGenerators S, closure_printedGenerators S⟩,
    (SimpleKazhdanSofic.printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl).2.2.2.1⟩

/-- **Ingredient: finite models** (tex l.125–135): periodic sequences with the words of length
`2ℓ + 1` of `X` (tex l.125–126); the models of `ProofRestModels` (cyclic permutation matrix, diagonal
matrices; tex l.126–128); the marked limit of `SL_{3N}(F₂)` with expanding Cayley graphs
(tex l.129–130); matricial maps `φ_k` whose finite models `EL₃(M_{N_k}(F₂)) ≅ SL_{3N_k}(F₂)` are
quotients of the Kazhdan group `EL₃(F₂⟨S⟩)` and form expanders (tex l.131–134); and `G_X` an
expander limit of the `SL_{3N}(F₂)` in the printed sense (tex l.134–135). -/
abbrev IngredientsFiniteModels (S : Subshift A ℤ) : Prop :=
  (∀ ℓ m₀ : ℕ, ∃ (m : ℕ) (_ : NeZero m) (y : ZMod m → A), m₀ ≤ m ∧
    (∀ n : ZMod m,
      (fun j : Fin (2 * ℓ + 1) => y (n + (j : ℕ))) ∈ WordGraph.language S.carrier (2 * ℓ + 1)) ∧
    ∀ u ∈ WordGraph.language S.carrier (2 * ℓ + 1),
      ∃ n : ZMod m, (fun j : Fin (2 * ℓ + 1) => y (n + (j : ℕ))) = u) ∧
  (∀ x ∈ S.carrier, ProofRestModels S x) ∧
  PrintedMarkedLimitExpanders S 3 ∧
  (∃ (N : ℕ → ℕ) (φ : ∀ k, R S → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
    IsMatricialVia (printedGenerators S) N φ ∧
    HasKazhdanPropertyT.{0, 0}
      ↥(elementaryGroup (Fin 3) (FreeAlgebra (ZMod 2) ↥(printedGenerators S))) ∧
    (∀ k, Function.Surjective (elementaryGroupMap (ι := Fin 3)
      (FreeAlgebra.lift (ZMod 2) fun s : ↥(printedGenerators S) => φ k s).toRingHom)) ∧
    (∀ k, Nonempty (↥(elementaryGroup (Fin 3) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) ≃*
      Matrix.SpecialLinearGroup (Fin 3 × Fin (N k)) (ZMod 2))) ∧
    SimpleKazhdanSofic.IsExpanderFamily (SK04.matricialMarking 3 (printedGenerators S) N φ)) ∧
  SK01.IsExpanderLimitOfClass SK01.IsFiniteSimpleSL3NF2 (G S)

theorem ingredients_finiteModels (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) : IngredientsFiniteModels S := by
  obtain ⟨hinfG, -, hsimple, -, hlimit, -, -, -⟩ :=
    SimpleKazhdanSofic.printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  obtain ⟨N, φ, hφ⟩ := periodicMatricial_printed A S hinf hmin
  haveI : IsSimpleGroup ↥(elementaryGroup (Fin 3) (R S)) := hsimple
  haveI : Infinite ↥(elementaryGroup (Fin 3) (R S)) := hinfG
  refine ⟨exists_periodic_sameWords_carrier S hinf hmin, fun _ hx => rest_models S hinf hmin hx,
    hlimit, ⟨N, φ, hφ,
      hasKazhdanPropertyT_elementaryGroup_freeAlgebra ↥(printedGenerators S) 3 le_rfl,
      fun k => elementaryGroupMap_surjective_of_surjective (ι := Fin 3)
        (FreeAlgebra.lift (ZMod 2) fun s : ↥(printedGenerators S) => φ k s).toRingHom
        (SimpleKazhdanSofic.lift_surjective_of_closure (printedGenerators S) (φ k) (hφ.2.2.1 k)),
      fun k => ⟨elementaryBlockEquivSL 3 le_rfl (N k) (hφ.1 k)⟩,
      SK04.isExpanderFamily_matricial 3 le_rfl (printedGenerators S) (one_mem_printedGenerators S)
        (closure_printedGenerators S) N hφ.1 φ
        (by unfold SK04.IsPrintedMatricial; exact ⟨hφ.2.1, hφ.2.2.1, hφ.2.2.2⟩)⟩,
    (main_printed_sk01 A S hinf hmin).2.2.2.2.1⟩

end Subshift

/-! ## Simplicity: the clopen tower -/

/-- A normal subgroup that meets the image of a simple group nontrivially contains the whole image
(tex l.122–123: "So it contains this group"). -/
theorem ingredients_normal_contains_copy {Q G : Type*} [Group Q] [IsSimpleGroup Q] [Group G]
    (H : Q →* G) (K : Subgroup G) (hK : K.Normal) {x : Q} (hx : x ≠ 1) (hxK : H x ∈ K) (y : Q) :
    H y ∈ K := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.comap H) (hK.comap H) with h | h
  · have hx' : x ∈ K.comap H := hxK
    rw [h, Subgroup.mem_bot] at hx'
    exact absurd hx' hx
  · have hy : y ∈ K.comap H := by
      rw [h]
      exact Subgroup.mem_top y
    exact hy

/-- **Ingredient: simplicity** (tex l.120–124), for a minimal topologically free action on a compact
totally separated space, `R = LC(Z, F₂) ⋊ Λ` and `n ≥ 3`:
`GL_d(F₂)` is simple for `d ≥ 3`; every nontrivial normal subgroup `K` of `EL_n(R)` contains a
nontrivial element of `M_n(A_V)` over a clopen tower `(V, B)` (`GeneralCommutatorWitness`); each tower
with `1 ∈ B` gives a finite simple group `GL_{n×B}(F₂)` embedded in `EL_n(R)`, sending transvections
to elementary matrices `e_pq(ε_ab)`, and a normal subgroup meeting the copy nontrivially contains all
of it; and minimality gives `K = EL_n(R)`. -/
def PrintedIngredientsSimplicity : Prop :=
  (∀ d : ℕ, 3 ≤ d → IsSimpleGroup (Matrix (Fin d) (Fin d) (ZMod 2))ˣ) ∧
  ∀ (Λ Z : Type) [Group Λ] [DecidableEq Λ] [TopologicalSpace Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))]
    [TotallySeparatedSpace Z] [CompactSpace Z] [MulAction.IsMinimal Λ Z],
    (∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z)) →
    (∀ ξ : Λ, ξ ≠ 1 → interior {z : Z | ξ • z = z} = ∅) →
    ∀ n : ℕ, 3 ≤ n →
      GeneralCommutatorWitness (General.coeffHom Λ Z) (General.unitHom Λ Z) n ∧
      (∀ (B : Finset Λ) (V : Set Z) (hV : IsClopen V), TranslatesDisjoint B V → V.Nonempty →
        (1 : Λ) ∈ B →
        IsSimpleGroup (Matrix (Fin n × B) (Fin n × B) (ZMod 2))ˣ ∧
        ∃ H : (Matrix (Fin n × B) (Fin n × B) (ZMod 2))ˣ →*
            ↥(elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)),
          Function.Injective H ∧
          (∀ (p q : Fin n) (hpq : p ≠ q) (a b : B) (h : ((p, a) : Fin n × B) ≠ (q, b)),
            ((H (elementaryUnit (p, a) (q, b) h (1 : ZMod 2)) :
                ↥(elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))) :
              (Matrix (Fin n) (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ))ˣ) =
              elementaryUnit p q hpq
                (SimpleKazhdanSofic.epsilon (General.coeffHom Λ Z) (General.unitHom Λ Z) hV a b)) ∧
          ∀ K : Subgroup ↥(elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)),
            K.Normal → ∀ x, x ≠ 1 → H x ∈ K → ∀ y, H y ∈ K) ∧
      ∀ K : Subgroup ↥(elementaryGroup (Fin n) (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)),
        K.Normal → K ≠ ⊥ → K = ⊤

/-- **Ingredient: simplicity** (tex l.120–124), unconditionally. -/
theorem printedIngredientsSimplicity : PrintedIngredientsSimplicity := by
  refine ⟨fun d hd => SK02.stepTwo_glSimple (Fin d) (by rw [Fintype.card_fin]; exact hd), ?_⟩
  intro Λ _ _ _ _ _ _ _ _ _ _ hact hfree n hn
  refine ⟨SK02.stepTwo_commutatorWitness hact hfree (by omega),
    fun B V hV hdisj hne h1 => ?_,
    fun K hK hne => SK02.stepThree_normalSubgroupEqTop hact hfree hn K hK hne⟩
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨H, hinj, hmem, htrans, -⟩ := SK02.stepTwo_towerCopy (ι := Fin n) hact hV hdisj hne
  have hcard : 3 ≤ Fintype.card (Fin n × B) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    nlinarith [Finset.card_pos.2 (⟨(1 : Λ), h1⟩ : B.Nonempty)]
  haveI hQ : IsSimpleGroup (Matrix (Fin n × B) (Fin n × B) (ZMod 2))ˣ :=
    SK02.stepTwo_glSimple (Fin n × B) hcard
  refine ⟨hQ, H.codRestrict _ hmem, (MonoidHom.injective_codRestrict H _ hmem).2 hinj,
    fun p q hpq a b h => htrans p q hpq a b h, fun K hK x hx hxK y => ?_⟩
  exact ingredients_normal_contains_copy (H.codRestrict _ hmem) K hK hx hxK y

/-! ## Figure `fig:models` -/

/-- **Figure (a)** (tex l.159–161): the `5`-periodic sequence `01001` has the words of length `3` of
the Fibonacci subshift; `u` acts as the rotation `P` (`P δ_t = δ_{t+1}`); and `e_1` acts as the
diagonal matrix with `1` at the shaded positions `1` and `4`. -/
abbrev PrintedFigureA : Prop :=
  WordGraph.word SK08.fibonacciY 0 5 = ![false, true, false, false, true] ∧
  Set.range (fun i : ℤ => WordGraph.word SK08.fibonacciY i 3) =
    WordGraph.language SK08.fibonacciSubshift.carrier 3 ∧
  SK08.fibonacciModel SK08.fibU = Pestov91.shiftMatrix (ZMod 2) 5 1 ∧
  (∀ t : ZMod 5, Matrix.mulVec (Pestov91.shiftMatrix (ZMod 2) 5 1) (Pi.single t 1) =
    Pi.single (t + 1) 1) ∧
  SK08.fibonacciModel (SK08.fibLetter true) =
    (Matrix.diagonal fun t : ZMod 5 =>
      if SK08.fibonacciY ((t.val : ℕ) : ℤ) = true then (1 : ZMod 2) else 0) ∧
  ∀ a b : Fin 5, SK08.fibonacciModel (SK08.fibLetter true) ((a : ℕ) : ZMod 5) ((b : ℕ) : ZMod 5) =
    SK08.displayedD a b

/-- **Figure (a)**, unconditionally. -/
theorem printedFigureA : PrintedFigureA :=
  ⟨SK08.fibonacciPeriodicWords.1, SK08.fibonacciPeriodicWords.2.2.1, SK08.fibonacciModel_unit,
    SK08.fibonacciDisplay.2.1, SK08.fibonacciModel_letter true, SK08.fibonacciDisplay.2.2.2.2⟩

/-- **Figure (b)** (tex l.161–162): for a clopen `V` whose translates `aV`, `a ∈ B`, are pairwise
disjoint, `ab⁻¹` moves `bV` to `aV`, `ε_ab = e_{aV} u_{ab⁻¹}`, and the `ε_ab` multiply as matrix units:
`ε_ab ε_a'b' = δ_ba' ε_ab'`. -/
def PrintedFigureB : Prop :=
  ∀ (Λ Z : Type) [Group Λ] [DecidableEq Λ] [TopologicalSpace Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] [MulSemiringAction Λ (LocallyConstant Z (ZMod 2))],
    (∀ (ξ : Λ) (f : LocallyConstant Z (ZMod 2)) (z : Z), (ξ • f) z = f (ξ⁻¹ • z)) →
    ∀ (B : Finset Λ) (V : Set Z) (hV : IsClopen V), TranslatesDisjoint B V → ∀ a b : Λ,
      (a * b⁻¹) • (b • V) = a • V ∧
      SimpleKazhdanSofic.epsilon (General.coeffHom Λ Z) (General.unitHom Λ Z) hV a b =
        General.coeffHom Λ Z (LocallyConstant.charFn (ZMod 2) (SimpleKazhdanSofic.isClopen_smul a hV)) *
          ((General.unitHom Λ Z (a * b⁻¹) : (SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ)ˣ) :
            SkewMonoidAlgebra (LocallyConstant Z (ZMod 2)) Λ) ∧
      ∀ a' b' : Λ, b ∈ B → a' ∈ B →
        SimpleKazhdanSofic.epsilon (General.coeffHom Λ Z) (General.unitHom Λ Z) hV a b *
            SimpleKazhdanSofic.epsilon (General.coeffHom Λ Z) (General.unitHom Λ Z) hV a' b' =
          if b = a' then
            SimpleKazhdanSofic.epsilon (General.coeffHom Λ Z) (General.unitHom Λ Z) hV a b'
          else 0

/-- **Figure (b)**, unconditionally. -/
theorem printedFigureB : PrintedFigureB := by
  intro _ _ _ _ _ _ _ _ hact B V hV hdisj a b
  refine ⟨by rw [smul_smul, inv_mul_cancel_right], rfl, fun a' b' hb ha' => ?_⟩
  exact SK02.stepTwo_epsilon_mul_epsilon hact hV hdisj (a := a) (b' := b') hb ha'

/-! ## The ingredients as one closed statement -/

/-- **The three ingredients of the proof** (tex l.113–135) and Figure `fig:models` (tex l.159–163):
for every infinite minimal subshift over a finite alphabet, property (T), simplicity of `G_X` and the
finite models; the simplicity mechanism over a clopen tower; and the two panels of the figure. -/
def PrintedProofIngredients : Prop :=
  (∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A] [Finite A]
    (S : Subshift A ℤ), Infinite S.carrier → IsMinimal S →
      IngredientsPropertyT S ∧ IsSimpleGroup (G S) ∧ IngredientsFiniteModels S) ∧
  PrintedIngredientsSimplicity ∧ PrintedFigureA ∧ PrintedFigureB

/-- **The three ingredients of the proof and `fig:models`**, unconditionally. -/
theorem printedProofIngredients : PrintedProofIngredients := by
  refine ⟨?_, printedIngredientsSimplicity, printedFigureA, printedFigureB⟩
  intro A _ _ _ _ S hinf hmin
  exact ⟨ingredients_propertyT S hinf hmin,
    (SimpleKazhdanSofic.printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl).2.2.1,
    ingredients_finiteModels S hinf hmin⟩

#audit_axioms GroupApproximation.Full.SK05.ingredients_propertyT
#audit_axioms GroupApproximation.Full.SK05.ingredients_finiteModels
#audit_axioms GroupApproximation.Full.SK05.ingredients_normal_contains_copy
#audit_closed_axioms GroupApproximation.Full.SK05.printedIngredientsSimplicity
#audit_closed_axioms GroupApproximation.Full.SK05.printedFigureA
#audit_closed_axioms GroupApproximation.Full.SK05.printedFigureB
#audit_closed_axioms GroupApproximation.Full.SK05.printedProofIngredients

end GroupApproximation.Full.SK05
