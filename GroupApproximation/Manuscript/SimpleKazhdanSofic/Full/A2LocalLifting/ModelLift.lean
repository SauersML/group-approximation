import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.Property
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.TraceVanishing
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Analysis.AmenableTraceHyperlinear
import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Analysis.TracialQuotientCStar
import GroupApproximation.Analysis.SoficHyperlinearTrace
import GroupApproximation.Analysis.ShulmanTraceFactorization
import GroupApproximation.Analysis.MaximalCStarKazhdanAverage
import GroupApproximation.Meta.AxiomGuard

/-!
# The model representation and the generator operator systems (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–56 (table row A2): Ozawa's remark that the
full C⋆-algebra of an infinite simple hyperlinear Kazhdan group has no local lifting property.  This
file holds the pieces of the factorization-through-local-lifting step that do not use the LLP.

* `euclideanCoordinateStarAlgHom n`: evaluation of a bounded matrix sequence at `n`, followed into
  `B(ℓ²(Fin |X n|))`, as a unital ⋆-homomorphism.
* `modelUnitaryHom M`: the unitaries of a trace-preserving matrix model become a group homomorphism
  into the unitary group of the tracial matrix quotient `∏ M_{k(n)} / J₂` along `atTop`;
  `exists_modelLift` extends it to `C⋆(G)`.
* `generatorSystem (generatorSet F)`: the span of the canonical generators over `{1} ∪ F ∪ F·F` and
  its inverses, a finite-dimensional operator system.

This is a fork, into lane `A2LocalLifting`, of the first half of the never-wired module
`Analysis/LocalLiftingFactorization.lean` (left untouched).

Ozawa, *About the QWEP conjecture*, Internat. J. Math. **15** (2004), preprint p. 24.
-/

namespace GroupApproximation
namespace Full
namespace A2LocalLifting

open Filter Quasidiagonal TracialUltraproduct ShulmanTrace
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Coordinates of the bounded matrix product -/

section Coordinates

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- Evaluation at one coordinate, followed into `B(ℓ²(Fin |X n|))`, as a unital ⋆-homomorphism
(row A2, tex l.54–56). -/
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
    rw [Algebra.algebraMap_eq_smul_one z, Algebra.algebraMap_eq_smul_one z]
    show euclideanize (X n) (z • (1 : ModelBoundedSequence X) n) = z • 1
    rw [map_smul, modelSeq_one_apply, euclideanize_one]
  map_star' a := by
    show euclideanize (X n) ((star a) n) = star (euclideanize (X n) (a n))
    rw [modelSeq_star_apply, euclideanize_star]

theorem euclideanCoordinateStarAlgHom_apply (n : ℕ) (a : ModelBoundedSequence X) :
    euclideanCoordinateStarAlgHom n a = euclideanize (X n) (a n) := rfl

end Coordinates

/-- The bundled quotient map acts as the quotient ring map. -/
theorem tracialMatrixQuotientQuotient_apply (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (l : Filter ℕ) (a : ModelBoundedSequence X) :
    tracialMatrixQuotientQuotient X l a = tracialMatrixQuotientMk X l a := rfl

/-- A unitary that is its own square is `1`. -/
theorem eq_one_of_mem_unitary_of_eq_mul_self {R : Type*} [Monoid R] [StarMul R] {u : R}
    (hu : u ∈ unitary R) (h : u = u * u) : u = 1 :=
  calc u = star u * u * u := by rw [(Unitary.mem_iff.mp hu).1, one_mul]
    _ = star u * (u * u) := mul_assoc _ _ _
    _ = star u * u := by rw [← h]
    _ = 1 := (Unitary.mem_iff.mp hu).1

/-! ## The model representation in the tracial matrix quotient -/

section Model

variable {G : Type} [Group G] (M : TracePreservingMatrixModel G)

local instance modelNonemptyForModelLift (n : ℕ) : Nonempty (M.model n) :=
  Fintype.card_pos_iff.mp (M.modelNonempty n)

theorem norm_modelUnitaryMatrix_le_one (n : ℕ) (g : G) :
    ‖(M.map n g : Matrix (M.model n) (M.model n) ℂ)‖ ≤ 1 := by
  haveI : Nontrivial (Matrix (M.model n) (M.model n) ℂ) := by
    refine nontrivial_of_ne 1 0 fun h ↦ ?_
    have h1 : ‖(1 : Matrix (M.model n) (M.model n) ℂ)‖ = 1 := norm_one
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  exact le_of_eq (CStarRing.norm_of_mem_unitary (M.map n g).2)

/-- The model unitaries of one group element, as a bounded sequence (row A2, tex l.54–56). -/
def modelUnitarySeq (g : G) : ModelBoundedSequence M.model :=
  boundedSeqOfBound (fun n ↦ (M.map n g : Matrix (M.model n) (M.model n) ℂ))
    (fun n ↦ norm_modelUnitaryMatrix_le_one M n g)

theorem modelUnitarySeq_apply (g : G) (n : ℕ) :
    modelUnitarySeq M g n = (M.map n g : Matrix (M.model n) (M.model n) ℂ) := rfl

/-- The multiplicative defect of the model is Hilbert–Schmidt null along `atTop`. -/
theorem isHilbertSchmidtNull_modelUnitarySeq_mul (g h : G) :
    IsHilbertSchmidtNull M.model atTop
      (modelUnitarySeq M (g * h) - modelUnitarySeq M g * modelUnitarySeq M h) := by
  rw [isHilbertSchmidtNull_iff_sq]
  have hkey : ∀ n, hsNormSq (M.model n)
      ((modelUnitarySeq M (g * h) - modelUnitarySeq M g * modelUnitarySeq M h) n) =
        hsDistSq (M.model n) (M.map n (g * h) : Matrix (M.model n) (M.model n) ℂ)
          ((M.map n g : Matrix (M.model n) (M.model n) ℂ) * M.map n h) := by
    intro n
    rw [modelSeq_sub_apply, modelSeq_mul_apply, modelUnitarySeq_apply, modelUnitarySeq_apply,
      modelUnitarySeq_apply]
    rfl
  refine tendsto_zero_of_forall_eventually_lt (fun n ↦ hsNormSq_nonneg _ _) fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := M.asymptoticallyMultiplicative g h (ε / 2) (half_pos hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  rw [hkey n]
  exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)

/-- The class of a model sequence is unitary: each coordinate is exactly unitary. -/
theorem mk_modelUnitarySeq_mem_unitary (g : G) :
    tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M g)
      ∈ unitary (TracialMatrixQuotient M.model atTop) := by
  rw [Unitary.mem_iff, tracialMatrixQuotient_star_mk, ← map_mul, ← map_mul]
  constructor
  · have hnull : IsHilbertSchmidtNull M.model atTop
        (star (modelUnitarySeq M g) * modelUnitarySeq M g - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply, modelSeq_one_apply,
        modelUnitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff'.mp (M.map n g).2
      rw [hu, sub_self]
    rw [mk_eq_mk_of_isHilbertSchmidtNull hnull, map_one]
  · have hnull : IsHilbertSchmidtNull M.model atTop
        (modelUnitarySeq M g * star (modelUnitarySeq M g) - 1) := by
      refine isHilbertSchmidtNull_of_forall_eq_zero fun n ↦ ?_
      rw [modelSeq_sub_apply, modelSeq_mul_apply, modelSeq_star_apply, modelSeq_one_apply,
        modelUnitarySeq_apply]
      have hu := Matrix.mem_unitaryGroup_iff.mp (M.map n g).2
      rw [hu, sub_self]
    rw [mk_eq_mk_of_isHilbertSchmidtNull hnull, map_one]

/-- **The model representation** (row A2, tex l.54–56): the model unitaries become a group
homomorphism into the unitary group of the `atTop` tracial matrix quotient. -/
def modelUnitaryHom : G →* unitary (TracialMatrixQuotient M.model atTop) where
  toFun g := ⟨tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M g),
    mk_modelUnitarySeq_mem_unitary M g⟩
  map_one' := by
    apply Subtype.ext
    show tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M 1) = 1
    have hq : tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M (1 * 1))
        = tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M 1 * modelUnitarySeq M 1) :=
      mk_eq_mk_of_isHilbertSchmidtNull (isHilbertSchmidtNull_modelUnitarySeq_mul M 1 1)
    rw [mul_one (1 : G), map_mul (tracialMatrixQuotientMk M.model atTop)] at hq
    exact eq_one_of_mem_unitary_of_eq_mul_self (mk_modelUnitarySeq_mem_unitary M 1) hq
  map_mul' g h := by
    apply Subtype.ext
    show tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M (g * h))
      = tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M g)
        * tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M h)
    rw [← map_mul]
    exact mk_eq_mk_of_isHilbertSchmidtNull (isHilbertSchmidtNull_modelUnitarySeq_mul M g h)

/-- The model representation extends to the maximal group C⋆-algebra (row A2, tex l.54–56). -/
theorem exists_modelLift :
    ∃ π : MaximalGroupCStar G →⋆ₐ[ℂ] TracialMatrixQuotient M.model atTop,
      ∀ g : G, π (maximalGroupCStarGenerator G g)
        = tracialMatrixQuotientMk M.model atTop (modelUnitarySeq M g) := by
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

/-- The span of the canonical generators over a finite set (row A2, tex l.54–56). -/
abbrev generatorSystem (T : Finset G) : Submodule ℂ (MaximalGroupCStar G) :=
  Submodule.span ℂ (maximalGroupCStarGenerator G '' (T : Set G))

theorem generator_mem_generatorSystem {T : Finset G} {g : G} (hg : g ∈ T) :
    maximalGroupCStarGenerator G g ∈ generatorSystem T :=
  Submodule.subset_span ⟨g, hg, rfl⟩

instance finiteDimensional_generatorSystem (T : Finset G) :
    FiniteDimensional ℂ (generatorSystem T) :=
  Module.Finite.span_of_finite ℂ (T.finite_toSet.image _)

/-- The generator span over a set containing `1` and closed under inverses is an operator
system (row A2, tex l.54–56). -/
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

end

end A2LocalLifting
end Full
end GroupApproximation

open GroupApproximation.Full.A2LocalLifting

#audit_closed_axioms exists_modelLift
#audit_closed_axioms isOperatorSystem_generatorSystem
