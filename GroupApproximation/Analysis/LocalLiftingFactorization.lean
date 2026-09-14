import GroupApproximation.Analysis.LocalLiftingProperty
import GroupApproximation.Analysis.OperatorSystemMatrixArveson
import GroupApproximation.Analysis.MatrixModelFormPositivity
import GroupApproximation.Analysis.HyperlinearTraceVanishingModels
import GroupApproximation.Analysis.AmenableTraceGeneratorDense
import GroupApproximation.Analysis.AmenableTraceHyperlinear
import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Analysis.TracialQuotientCStar
import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Meta.AxiomGuard

/-!
# The local lifting property and a trace-preserving matrix model give the
# factorization property

Ozawa, *About the QWEP conjecture*, Internat. J. Math. **15** (2004), p. 24 of
the preprint: for a hyperlinear `Γ`, "because of the LLP of `C*𝔽_∞`, the trace
`τ_Γ` on `C*𝔽_∞` … is liftable".  The same argument with `C⋆(G)` in place of
`C⋆𝔽_∞` gives the implication behind p. 527 (preprint p. 26): a simple Kazhdan
hyperlinear group cannot have a full C⋆-algebra with the LLP.

`localLiftingFactorizationStatement_holds`: for a countable group `G`, if
`C⋆(G)` has the local lifting property and `G` has a trace-preserving unitary
matrix model, then `G` has the factorization property.  The factorization
property is at its trace side, `NinetyNineProblems.HasFactorizationProperty`.

Route.
1. The model unitaries represent `G` in the tracial matrix quotient
   `∏ M_{k(n)} / J₂` along `atTop`, which lifts to `π : C⋆(G) → ∏ M_{k(n)}/J₂`.
2. `π` is unital and completely positive.  The LLP lifts it on the
   finite-dimensional operator system spanned by the generators over
   `{1} ∪ F ∪ F·F` and its inverses.
3. Each coordinate of the lift, followed into `B(ℓ²)`, is completely positive
   on that operator system.  Arveson's theorem
   (`operatorSystemMatrixArvesonStatement_holds`) extends it to a unital
   completely positive map on `C⋆(G)`.
4. On generators the extended maps are the coordinates of the lift.  Their
   multiplicative defects and trace errors are Hilbert–Schmidt null, because
   the lift composed with the quotient map is `π`.
5. A diagonal choice over an exhaustion of `G` gives models on all generators,
   and the dense-generator upgrade
   (`Quasidiagonal.amenableTraceModel_of_dense_generators`) gives an amenable
   trace model.
-/

namespace GroupApproximation
namespace LocalLifting

open Filter Matrix CStarExactness Quasidiagonal TracialUltraproduct ShulmanTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The bounded matrix product is a C⋆-algebra, assembled from its existing
normed, star and complete structure. -/
local instance modelBoundedSequenceCStarAlgebraForLocalLifting
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CStarAlgebra (ModelBoundedSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := by
    constructor
    intro c x
    apply lp.ext
    funext n
    change star (c • x n) = star c • star (x n)
    rw [star_smul]

/-! ## Coordinates of the bounded matrix product -/

section Coordinates

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Evaluation at one coordinate, followed into `B(ℓ²(Fin |X n|))`, as a unital
⋆-homomorphism. -/
def euclideanCoordinateStarAlgHom (n : ℕ) :
    ModelBoundedSequence X →⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card (X n))) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card (X n)))) where
  toFun a := euclideanize (X n) (a n)
  map_one' := by
    show euclideanize (X n) ((1 : ModelBoundedSequence X) n) = 1
    exact euclideanize_one (X n)
  map_mul' a b := by
    show euclideanize (X n) ((a * b) n)
      = euclideanize (X n) (a n) * euclideanize (X n) (b n)
    rw [modelSeq_mul_apply, euclideanize_apply, euclideanize_apply,
      euclideanize_apply, map_mul, map_mul]
  map_zero' := by
    show euclideanize (X n) ((0 : ModelBoundedSequence X) n) = 0
    exact map_zero (euclideanize (X n))
  map_add' a b := by
    show euclideanize (X n) ((a + b) n)
      = euclideanize (X n) (a n) + euclideanize (X n) (b n)
    exact map_add (euclideanize (X n)) (a n) (b n)
  commutes' z := by
    show euclideanize (X n) ((algebraMap ℂ (ModelBoundedSequence X) z) n)
      = algebraMap ℂ _ z
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      modelSeq_smul_apply, modelSeq_one_apply, map_smul, euclideanize_one]
  map_star' a := by
    show euclideanize (X n) ((star a) n) = star (euclideanize (X n) (a n))
    rw [modelSeq_star_apply, euclideanize_star]

theorem euclideanCoordinateStarAlgHom_apply (n : ℕ) (a : ModelBoundedSequence X) :
    euclideanCoordinateStarAlgHom n a = euclideanize (X n) (a n) := rfl

end Coordinates

/-! ## The model representation in the tracial matrix quotient -/

section Model

variable {G : Type} [Group G] (M : TracePreservingMatrixModel G)

local instance modelNonemptyForLocalLifting (n : ℕ) : Nonempty (M.model n) :=
  Fintype.card_pos_iff.mp (M.modelNonempty n)

theorem norm_model_le_one (n : ℕ) (g : G) :
    ‖(M.map n g : Matrix (M.model n) (M.model n) ℂ)‖ ≤ 1 :=
  le_of_eq (CStarRing.norm_of_mem_unitary (M.map n g).2)

/-- The model unitaries of one group element, as a bounded sequence. -/
def modelSeq (g : G) : ModelBoundedSequence M.model :=
  boundedSeqOfBound (fun n ↦ (M.map n g : Matrix (M.model n) (M.model n) ℂ))
    (fun n ↦ norm_model_le_one M n g)

/-- The multiplicative defect of the model is Hilbert–Schmidt null along
`atTop`. -/
theorem isHilbertSchmidtNull_modelSeq_mul (g h : G) :
    IsHilbertSchmidtNull M.model atTop
      (modelSeq M (g * h) - modelSeq M g * modelSeq M h) := by
  rw [isHilbertSchmidtNull_iff_sq]
  refine tendsto_zero_of_forall_eventually_lt (fun n ↦ hsNormSq_nonneg _ _)
    fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := M.asymptoticallyMultiplicative g h (ε / 2) (half_pos hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)

/-- The class of a model sequence is unitary: each coordinate is exactly
unitary. -/
theorem mk_modelSeq_mem_unitary (g : G) :
    tracialMatrixQuotientMk M.model atTop (modelSeq M g)
      ∈ unitary (TracialMatrixQuotient M.model atTop) := by
  have hstar : star (tracialMatrixQuotientMk M.model atTop (modelSeq M g))
      = tracialMatrixQuotientMk M.model atTop (star (modelSeq M g)) :=
    tracialMatrixQuotient_star_mk M.model atTop (modelSeq M g)
  rw [Unitary.mem_iff, hstar, ← map_mul, ← map_mul]
  constructor
  · have hnull : IsHilbertSchmidtNull M.model atTop
        (star (modelSeq M g) * modelSeq M g - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply,
        modelSeq_one_apply]
      exact sub_eq_zero.mpr (Matrix.mem_unitaryGroup_iff'.mp (M.map n g).2)
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := M.model) (l := atTop) hnull
    rw [this, map_one]
  · have hnull : IsHilbertSchmidtNull M.model atTop
        (modelSeq M g * star (modelSeq M g) - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply,
        modelSeq_one_apply]
      exact sub_eq_zero.mpr (Matrix.mem_unitaryGroup_iff.mp (M.map n g).2)
    have := mk_eq_mk_of_isHilbertSchmidtNull (X := M.model) (l := atTop) hnull
    rw [this, map_one]

/-- **The model representation**: the model unitaries become a group
homomorphism into the unitary group of the `atTop` tracial matrix quotient. -/
def modelUnitaryHom : G →* unitary (TracialMatrixQuotient M.model atTop) where
  toFun g := ⟨tracialMatrixQuotientMk M.model atTop (modelSeq M g),
    mk_modelSeq_mem_unitary M g⟩
  map_one' := by
    apply Subtype.ext
    show tracialMatrixQuotientMk M.model atTop (modelSeq M 1) = 1
    have hnull := isHilbertSchmidtNull_modelSeq_mul M 1 1
    rw [mul_one] at hnull
    have hq := mk_eq_mk_of_isHilbertSchmidtNull (X := M.model) (l := atTop) hnull
    rw [map_mul] at hq
    have hstar := (Unitary.mem_iff.mp (mk_modelSeq_mem_unitary M 1)).1
    calc tracialMatrixQuotientMk M.model atTop (modelSeq M 1)
        = star (tracialMatrixQuotientMk M.model atTop (modelSeq M 1))
            * tracialMatrixQuotientMk M.model atTop (modelSeq M 1)
            * tracialMatrixQuotientMk M.model atTop (modelSeq M 1) := by
          rw [hstar, one_mul]
      _ = star (tracialMatrixQuotientMk M.model atTop (modelSeq M 1))
            * (tracialMatrixQuotientMk M.model atTop (modelSeq M 1)
              * tracialMatrixQuotientMk M.model atTop (modelSeq M 1)) :=
          mul_assoc _ _ _
      _ = star (tracialMatrixQuotientMk M.model atTop (modelSeq M 1))
            * tracialMatrixQuotientMk M.model atTop (modelSeq M 1) := by
          rw [← hq]
      _ = 1 := hstar
  map_mul' g h := by
    apply Subtype.ext
    show tracialMatrixQuotientMk M.model atTop (modelSeq M (g * h))
      = tracialMatrixQuotientMk M.model atTop (modelSeq M g)
        * tracialMatrixQuotientMk M.model atTop (modelSeq M h)
    rw [← map_mul]
    exact mk_eq_mk_of_isHilbertSchmidtNull (X := M.model) (l := atTop)
      (isHilbertSchmidtNull_modelSeq_mul M g h)

/-- The model representation extends to the maximal group C⋆-algebra. -/
theorem exists_modelLift :
    ∃ π : MaximalGroupCStar G →⋆ₐ[ℂ] TracialMatrixQuotient M.model atTop,
      ∀ g : G, π (maximalGroupCStarGenerator G g)
        = tracialMatrixQuotientMk M.model atTop (modelSeq M g) := by
  obtain ⟨π, hπ, -⟩ := maximalGroupCStar_existsUnique_lift G (modelUnitaryHom M)
  exact ⟨π, fun g ↦ hπ g⟩

end Model

/-! ## The operator system of a finite set of generators -/

section Generators

variable {G : Type} [Group G]

/-- `{1} ∪ F ∪ F·F`. -/
def generatorCore [DecidableEq G] (F : Finset G) : Finset G :=
  insert 1 (F ∪ (F ×ˢ F).image fun p : G × G ↦ p.1 * p.2)

/-- `{1} ∪ F ∪ F·F`, closed under inverses. -/
def generatorSet [DecidableEq G] (F : Finset G) : Finset G :=
  generatorCore F ∪ (generatorCore F).image fun g : G ↦ g⁻¹

theorem one_mem_generatorSet [DecidableEq G] (F : Finset G) :
    (1 : G) ∈ generatorSet F :=
  Finset.mem_union_left _ (Finset.mem_insert_self _ _)

theorem mem_generatorSet_of_mem [DecidableEq G] {F : Finset G} {g : G}
    (hg : g ∈ F) : g ∈ generatorSet F :=
  Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hg))

theorem mul_mem_generatorSet [DecidableEq G] {F : Finset G} {g h : G}
    (hg : g ∈ F) (hh : h ∈ F) : g * h ∈ generatorSet F :=
  Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩)))

theorem inv_mem_generatorSet [DecidableEq G] {F : Finset G} {g : G}
    (hg : g ∈ generatorSet F) : g⁻¹ ∈ generatorSet F := by
  rcases Finset.mem_union.mp hg with h | h
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, h, rfl⟩)
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    rw [inv_inv]
    exact Finset.mem_union_left _ hx

/-- The span of the canonical generators over a finite set. -/
abbrev generatorSystem (T : Finset G) : Submodule ℂ (MaximalGroupCStar G) :=
  Submodule.span ℂ (maximalGroupCStarGenerator G '' (T : Set G))

theorem generator_mem_generatorSystem {T : Finset G} {g : G} (hg : g ∈ T) :
    maximalGroupCStarGenerator G g ∈ generatorSystem T :=
  Submodule.subset_span ⟨g, hg, rfl⟩

instance finiteDimensional_generatorSystem (T : Finset G) :
    FiniteDimensional ℂ (generatorSystem T) :=
  Module.Finite.span_of_finite ℂ (T.finite_toSet.image _)

theorem isOperatorSystem_generatorSystem {T : Finset G} (h1 : (1 : G) ∈ T)
    (hinv : ∀ g ∈ T, g⁻¹ ∈ T) : IsOperatorSystem (generatorSystem T) := by
  refine ⟨?_, fun x hx ↦ ?_⟩
  · have h := generator_mem_generatorSystem (G := G) h1
    rwa [AmenableTraceHyperlinear.maximalGroupCStarGenerator_one] at h
  · induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨g, hg, rfl⟩ := hy
        rw [star_maximalGroupCStarGenerator]
        exact generator_mem_generatorSystem (hinv g hg)
    | zero =>
        rw [star_zero]
        exact zero_mem _
    | add y z _ _ hy hz =>
        rw [star_add]
        exact add_mem hy hz
    | smul c y _ hy =>
        rw [star_smul]
        exact Submodule.smul_mem _ _ hy

end Generators

/-! ## Unital ⋆-homomorphisms as completely positive linear maps -/

section StarAlgHomLinear

variable {A : Type*} {B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A unital ⋆-homomorphism, as a linear map, is completely positive. -/
theorem isCompletelyPositive_starAlgHom_toLinear (π : A →⋆ₐ[ℂ] B) :
    IsCompletelyPositive (π.toNonUnitalStarAlgHom : A →ₗ[ℂ] B) :=
  isCompletelyPositive_of_starAlgHom π.toNonUnitalStarAlgHom

theorem starAlgHom_toLinear_one (π : A →⋆ₐ[ℂ] B) :
    (π.toNonUnitalStarAlgHom : A →ₗ[ℂ] B) 1 = 1 :=
  map_one π

end StarAlgHomLinear

/-! ## Approximate models on a finite set of generators -/

section Approximation

variable {G : Type} [Group G]

/-- **One step of the diagonal argument.**  Under the LLP, a trace-preserving
matrix model gives, for every finite `F ⊆ G` and `ε > 0`, a unital completely
positive matrix model of `C⋆(G)` whose multiplicative defects on pairs of
generators over `F`, and whose trace errors on generators over `F`, are below
`ε`. -/
theorem exists_approximateModel
    (hLLP : HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G))
    (M : TracePreservingMatrixModel G) (F : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (_ : Nonempty Y)
      (φ : MaximalGroupCStar G →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ g ∈ F, ∀ h ∈ F, hsNorm Y
          (φ (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h)
            - φ (maximalGroupCStarGenerator G g)
              * φ (maximalGroupCStarGenerator G h)) < ε) ∧
      ∀ g ∈ F, ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g)
          - normTrace Y (φ (maximalGroupCStarGenerator G g))‖ < ε := by
  classical
  haveI : ∀ n, Nonempty (M.model n) := fun n ↦
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  obtain ⟨π, hπ⟩ := exists_modelLift M
  have hEsys : IsOperatorSystem (generatorSystem (generatorSet F)) :=
    isOperatorSystem_generatorSystem (one_mem_generatorSet F)
      (fun g hg ↦ inv_mem_generatorSet hg)
  have hsurj : Function.Surjective
      (tracialMatrixQuotientQuotient M.model atTop) :=
    tracialMatrixQuotientMk_surjective M.model atTop
  have hπcp := isCompletelyPositive_starAlgHom_toLinear π
  have hπ1 := starAlgHom_toLinear_one π
  obtain ⟨ψ, hψcp, hψ1, hψlift⟩ :=
    hLLP (ModelBoundedSequence M.model) (TracialMatrixQuotient M.model atTop)
      (tracialMatrixQuotientQuotient M.model atTop) hsurj _ hπcp hπ1
      (generatorSystem (generatorSet F)) hEsys inferInstance
  have hq : ∀ x : generatorSystem (generatorSet F),
      tracialMatrixQuotientMk M.model atTop (ψ x) = π x := fun x ↦ hψlift x
  -- the Arveson extensions of the coordinates
  have hext : ∀ n : ℕ, ∃ Ψ : MaximalGroupCStar G →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card (M.model n))) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card (M.model n)))),
      IsCompletelyPositive Ψ ∧ Ψ 1 = 1 ∧
        ∀ x : generatorSystem (generatorSet F),
          Ψ (x : MaximalGroupCStar G) = euclideanize (M.model n) ((ψ x) n) := by
    intro n
    have hcp' := hψcp.comp_starAlgHom (euclideanCoordinateStarAlgHom (X := M.model) n)
    obtain ⟨Ψ, hΨcp, hΨ1, hΨext⟩ :=
      operatorSystemMatrixArvesonStatement_holds.{1} (MaximalGroupCStar G)
        (generatorSystem (generatorSet F)) hEsys (Fintype.card (M.model n)) _ hcp'
        (fun x hx ↦ by
          show euclideanCoordinateStarAlgHom (X := M.model) n (ψ x) = 1
          rw [hψ1 x hx, map_one])
    exact ⟨Ψ, hΨcp, hΨ1, fun x ↦ hΨext x⟩
  choose Ψ hΨcp hΨ1 hΨext using hext
  have hφu : ∀ (n : ℕ) (g : G) (hg : g ∈ generatorSet F),
      (matrixOfEuclidean (M.model n)).comp (Ψ n) (maximalGroupCStarGenerator G g)
        = (ψ ⟨maximalGroupCStarGenerator G g, generator_mem_generatorSystem hg⟩) n := by
    intro n g hg
    rw [LinearMap.comp_apply]
    have h := hΨext n ⟨maximalGroupCStarGenerator G g, generator_mem_generatorSystem hg⟩
    rw [show ((⟨maximalGroupCStarGenerator G g, generator_mem_generatorSystem hg⟩ :
        generatorSystem (generatorSet F)) : MaximalGroupCStar G)
          = maximalGroupCStarGenerator G g from rfl] at h
    rw [h, matrixOfEuclidean_euclideanize]
  -- the multiplicative defects are null
  have hmulnull : ∀ (g : G) (hg : g ∈ F) (h : G) (hh : h ∈ F),
      IsHilbertSchmidtNull M.model atTop
        (ψ ⟨maximalGroupCStarGenerator G (g * h),
            generator_mem_generatorSystem (mul_mem_generatorSet hg hh)⟩
          - ψ ⟨maximalGroupCStarGenerator G g,
              generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
            * ψ ⟨maximalGroupCStarGenerator G h,
              generator_mem_generatorSystem (mem_generatorSet_of_mem hh)⟩) := by
    intro g hg h hh
    rw [← tracialMatrixQuotientMk_eq_zero_iff, map_sub, map_mul, hq, hq, hq]
    show π (maximalGroupCStarGenerator G (g * h))
        - π (maximalGroupCStarGenerator G g) * π (maximalGroupCStarGenerator G h) = 0
    rw [← map_mul, maximalGroupCStarGenerator_mul, sub_self]
  -- the lift is close to the model at each generator
  have htrnull : ∀ (g : G) (hg : g ∈ F),
      IsHilbertSchmidtNull M.model atTop
        (ψ ⟨maximalGroupCStarGenerator G g,
            generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
          - modelSeq M g) := by
    intro g hg
    rw [← tracialMatrixQuotientMk_eq_zero_iff, map_sub, hq]
    show π (maximalGroupCStarGenerator G g)
        - tracialMatrixQuotientMk M.model atTop (modelSeq M g) = 0
    rw [hπ g, sub_self]
  have hevmul : ∀ᶠ n in atTop, ∀ g ∈ F, ∀ h ∈ F, hsNorm (M.model n)
      ((matrixOfEuclidean (M.model n)).comp (Ψ n)
          (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h)
        - (matrixOfEuclidean (M.model n)).comp (Ψ n) (maximalGroupCStarGenerator G g)
          * (matrixOfEuclidean (M.model n)).comp (Ψ n)
            (maximalGroupCStarGenerator G h)) < ε := by
    rw [eventually_all_finset]
    intro g hg
    rw [eventually_all_finset]
    intro h hh
    filter_upwards [eventually_lt_of_tendsto_zero (hmulnull g hg h hh) hε] with n hn
    rw [maximalGroupCStarGenerator_mul, hφu n (g * h) (mul_mem_generatorSet hg hh),
      hφu n g (mem_generatorSet_of_mem hg), hφu n h (mem_generatorSet_of_mem hh)]
    rw [modelSeq_sub_apply, modelSeq_mul_apply] at hn
    exact hn
  have hevtr : ∀ᶠ n in atTop, ∀ g ∈ F,
      ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g)
        - normTrace (M.model n)
          ((matrixOfEuclidean (M.model n)).comp (Ψ n)
            (maximalGroupCStarGenerator G g))‖ < ε := by
    rw [eventually_all_finset]
    intro g hg
    have hz : Tendsto (fun n ↦ normTrace (M.model n)
        ((ψ ⟨maximalGroupCStarGenerator G g,
            generator_mem_generatorSystem (mem_generatorSet_of_mem hg)⟩
          - modelSeq M g) n)) atTop (nhds 0) :=
      squeeze_zero_norm (fun n ↦ norm_normTrace_le_hsNorm (M.model n) _)
        (htrnull g hg)
    have htr : Tendsto (fun n ↦ normTrace (M.model n)
        (M.map n g : Matrix (M.model n) (M.model n) ℂ)) atTop
        (nhds (canonicalMaximalTrace G (maximalGroupCStarGenerator G g))) := by
      by_cases hg1 : g = 1
      · subst hg1
        rw [canonicalMaximalTrace_generator_one]
        exact M.trace_tendsto_one
      · rw [canonicalMaximalTrace_generator_of_ne_one G hg1]
        exact M.trace_tendsto_ne g hg1
    have hsum := htr.add hz
    rw [add_zero] at hsum
    have hsum' : Tendsto (fun n ↦ normTrace (M.model n)
        ((matrixOfEuclidean (M.model n)).comp (Ψ n)
          (maximalGroupCStarGenerator G g))) atTop
        (nhds (canonicalMaximalTrace G (maximalGroupCStarGenerator G g))) := by
      refine hsum.congr fun n ↦ ?_
      rw [hφu n g (mem_generatorSet_of_mem hg), modelSeq_sub_apply, normTrace_sub]
      have hseq : (modelSeq M g) n = (M.map n g : Matrix (M.model n) (M.model n) ℂ) := rfl
      rw [hseq]
      ring
    filter_upwards [Metric.tendsto_nhds.mp hsum' ε hε] with n hn
    rw [dist_eq_norm, norm_sub_rev] at hn
    exact hn
  obtain ⟨n, hn1, hn2⟩ := (hevmul.and hevtr).exists
  exact ⟨M.model n, inferInstance, (matrixOfEuclidean (M.model n)).comp (Ψ n),
    by rw [LinearMap.comp_apply, hΨ1 n, matrixOfEuclidean_one],
    isCompletelyPositiveOnMatrices_matrixOfEuclidean (M.model n) (Ψ n) (hΨcp n),
    hn1, hn2⟩

end Approximation

/-! ## The theorem -/

/-- **The local lifting property and a trace-preserving matrix model give the
factorization property**, as a closed proposition. -/
def LocalLiftingFactorizationStatement : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G) →
      HasTracePreservingMatrixModel G → NinetyNineProblems.HasFactorizationProperty G

/-- **The local lifting property and a trace-preserving matrix model give the
factorization property.**  Ozawa's p. 24 argument: local ucp lifts on
generator operator systems, Arveson extension, a diagonal choice, and the
dense-generator upgrade to an amenable trace model. -/
theorem localLiftingFactorizationStatement_holds :
    LocalLiftingFactorizationStatement := by
  intro G _ _ hLLP hM
  classical
  obtain ⟨M⟩ := hM
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat G
  have hstep : ∀ k : ℕ, ∃ (Y : FiniteModel) (_ : Nonempty Y)
      (φ : MaximalGroupCStar G →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ g ∈ (Finset.range (k + 1)).image e, ∀ h ∈ (Finset.range (k + 1)).image e,
        hsNorm Y
          (φ (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h)
            - φ (maximalGroupCStarGenerator G g)
              * φ (maximalGroupCStarGenerator G h)) < 1 / ((k : ℝ) + 1)) ∧
      ∀ g ∈ (Finset.range (k + 1)).image e,
        ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g)
          - normTrace Y (φ (maximalGroupCStarGenerator G g))‖ < 1 / ((k : ℝ) + 1) :=
    fun k ↦ exists_approximateModel hLLP M ((Finset.range (k + 1)).image e)
      (by positivity)
  choose Y hY φ hone hcp hmul htr using hstep
  haveI : ∀ k, Nonempty (Y k) := hY
  have hcontr : ∀ k a, ‖φ k a‖ ≤ ‖a‖ := fun k a ↦ ucp_norm_le (φ k) (hone k) (hcp k) a
  have hmem : ∀ g : G, ∀ᶠ k in atTop, g ∈ (Finset.range (k + 1)).image e := by
    intro g
    obtain ⟨i, rfl⟩ := he g
    exact Filter.eventually_atTop.mpr
      ⟨i, fun k hk ↦ Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩⟩
  have hsmall : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmulgen : ∀ a ∈ Set.range (maximalGroupCStarGenerator G),
      ∀ b ∈ Set.range (maximalGroupCStarGenerator G),
        Tendsto (fun k ↦ hsNorm (Y k) (φ k (a * b) - φ k a * φ k b)) atTop (nhds 0) := by
    rintro a ⟨g, rfl⟩ b ⟨h, rfl⟩
    refine squeeze_zero' (Eventually.of_forall fun k ↦ hsNorm_nonneg _ _) ?_ hsmall
    filter_upwards [hmem g, hmem h] with k hgk hhk
    exact (hmul k g hgk h hhk).le
  have htrgen : ∀ a ∈ Set.range (maximalGroupCStarGenerator G),
      Tendsto (fun k ↦ ‖canonicalMaximalTrace G a - normTrace (Y k) (φ k a)‖)
        atTop (nhds 0) := by
    rintro a ⟨g, rfl⟩
    refine squeeze_zero' (Eventually.of_forall fun k ↦ norm_nonneg _) ?_ hsmall
    filter_upwards [hmem g] with k hgk
    exact (htr k g hgk).le
  exact Nonempty.intro (amenableTraceModel_of_dense_generators φ hone hcp hcontr
    (canonicalMaximalTrace G) (Set.range (maximalGroupCStarGenerator G))
    (maximalGroupCStar_dense_span_generator G) hmulgen htrgen)

end

end LocalLifting
end GroupApproximation

open GroupApproximation.LocalLifting

#audit_axioms LocalLiftingFactorizationStatement
#audit_closed_axioms localLiftingFactorizationStatement_holds
