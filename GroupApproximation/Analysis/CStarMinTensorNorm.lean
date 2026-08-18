import GroupApproximation.Analysis.CStarStateGNS
import GroupApproximation.Analysis.CStarTensorProductAlgebra
import GroupApproximation.Analysis.CStarSeminormQuotient

/-!
# The canonical minimal tensor norm, and `A ⊗_min B` as a C⋆-algebra

## What this module builds

The tensor lane's spatial norm is attached to a *chosen* pair of faithful
representations, and its roadmap (`CStarTensorProduct.lean`) records the
canonical alternative: a supremum over a **set-sized family of
representations manufactured from states**.  This module executes that
alternative.  With the norm-attaining states of `CStarStateSeparation` and
the jointly isometric GNS family of `CStarStateGNS`:

* `minTensorNorm` is the pointwise supremum, over all pairs of states
  `(φ, ψ)`, of the spatial seminorm of the pair of GNS representations
  `(gnsRep φ, gnsRep ψ)`;
* it is a C⋆-seminorm by the supremum recipe
  (`isCStarSeminorm_iSup_starRep`), a **norm** because the GNS family
  separates points (`eq_zero_of_forall_spatialHom_gnsRep_eq_zero` -- the
  family-quantified form of the spatial lane's injectivity argument), and a
  **cross norm on the nose**: `minTensorNorm (a ⊗ₜ b) = ‖a‖ * ‖b‖`
  (`minTensorNorm_tmul`), the full strength the fixed-pair spatial norm
  could state only against `‖π a‖ * ‖ρ b‖`;
* `MinTensorProduct A B` is the completion, a C⋆-algebra by the
  `WithCStarNorm` chain, with the algebraic tensor product embedded
  isometrically and densely by `minTensorIn`.

## What canonicity does and does not mean here

The construction depends on no choices: the index is *every* state of each
factor, so `MinTensorProduct A B` is a canonical functorial object -- this is
what makes the notation `⊗_min` honest as a *definition*.  Two theorems about
it remain open, and neither is claimed:

* **Takesaki's identification** (Stage C.4 of the roadmap): that for any one
  faithful pair `(π, ρ)` the spatial norm equals `minTensorNorm`, i.e. that
  `A ⊗_{π,ρ} B ≅ A ⊗_min B`.  The supremum dominates no single pair and no
  single pair dominates the supremum, until that theorem is proved.
* **Minimality**: that `minTensorNorm` is the least C⋆-norm on `A ⊙ B`.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  With this module
the object `⊗_min` that the exactness vocabulary needs *exists*; `SO.16` and
`RE.05` remain **MISSING** pending the noncommutative C⋆-quotient (for
`IsExact` to be statable), the maximal norm (for nuclearity), and the
research-scale inputs the standing record in `CStarExactness.lean` itemises.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct InnerProductSpace

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]

/-! ## States exist -/

instance instNonemptyState : Nonempty (State A) :=
  ⟨(State.exists_star_mul_self (1 : A)).choose⟩

/-! ## The family of GNS pair representations -/

/-- The spatial representation of the algebraic tensor product attached to a
pair of states: the tensor product of their GNS representations. -/
noncomputable def gnsPairRep (p : State A × State B) :
    StarRep (A ⊗[ℂ] B) (p.1.GNSSpace ⊗[ℂ] p.2.GNSSpace) :=
  spatialRep p.1.gnsRep p.2.gnsRep

/-- **The canonical minimal tensor norm**: the supremum, over all pairs of
states, of the spatial seminorm of the pair of GNS representations. -/
noncomputable def minTensorNorm : (A ⊗[ℂ] B) → ℝ :=
  iSupSeminorm fun p : State A × State B => (gnsPairRep p).seminorm

theorem minTensorNorm_apply (x : A ⊗[ℂ] B) :
    minTensorNorm x
      = ⨆ p : State A × State B, spatialNorm p.1.gnsRep p.2.gnsRep x := rfl

/-- The family of spatial seminorms of GNS pairs is pointwise bounded: on an
elementary tensor by `‖a‖ * ‖b‖` through contractivity of each GNS
representation, and in general through subadditivity along any
decomposition. -/
theorem bddAbove_spatialNorm_gnsRep (x : A ⊗[ℂ] B) :
    BddAbove (Set.range fun p : State A × State B =>
      spatialNorm p.1.gnsRep p.2.gnsRep x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      rintro r ⟨p, rfl⟩
      show spatialNorm p.1.gnsRep p.2.gnsRep 0 ≤ 0
      rw [spatialNorm_apply, map_zero]
      exact le_of_eq ContinuousLinearMap.opNorm_zero
  | tmul a b =>
      refine ⟨‖a‖ * ‖b‖, ?_⟩
      rintro r ⟨p, rfl⟩
      show spatialNorm p.1.gnsRep p.2.gnsRep (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖
      rw [spatialNorm_tmul]
      exact mul_le_mul (p.1.norm_gnsRep_apply_le a)
        (p.2.norm_gnsRep_apply_le b) (norm_nonneg _) (norm_nonneg a)
  | add y z hy hz =>
      obtain ⟨Cy, hCy⟩ := hy
      obtain ⟨Cz, hCz⟩ := hz
      refine ⟨Cy + Cz, ?_⟩
      rintro r ⟨p, rfl⟩
      have h1 : spatialNorm p.1.gnsRep p.2.gnsRep (y + z)
          ≤ spatialNorm p.1.gnsRep p.2.gnsRep y
            + spatialNorm p.1.gnsRep p.2.gnsRep z :=
        (spatialNorm_isCStarSeminorm _ _).add_le y z
      exact h1.trans (add_le_add (hCy ⟨p, rfl⟩) (hCz ⟨p, rfl⟩))

/-! ## The GNS family separates the tensor product

The four-step skeleton of `spatialHom_injective`, with the single faithful
pair replaced by the family of all state pairs and the vector-functional
separation replaced by `eq_zero_of_forall_state_inner_eq_zero`. -/

/-- **Joint faithfulness of the GNS pair family**: an element of the
algebraic tensor product killed by every `gnsRep φ ⊗ gnsRep ψ` is zero. -/
theorem eq_zero_of_forall_spatialHom_gnsRep_eq_zero {x : A ⊗[ℂ] B}
    (hx : ∀ (φ : State A) (ψ : State B),
      spatialHom φ.gnsRep ψ.gnsRep x = 0) : x = 0 := by
  classical
  set c := Module.Basis.ofVectorSpace ℂ B with hc
  -- Steps 1 and 2: every first-variable slice vanishes, by separation on `B`.
  have hslice : ∀ (φ : State A) (ξ ξ' : φ.GNSSpace),
      sliceRight (vecFunctional φ.gnsRep ξ ξ') x = 0 := by
    intro φ ξ ξ'
    refine eq_zero_of_forall_state_inner_eq_zero _ fun ψ η η' => ?_
    have h := inner_spatialHom_apply φ.gnsRep ψ.gnsRep ξ ξ' η η' x
    rw [hx φ ψ] at h
    simp only [zero_apply, inner_zero_right, vecFunctional_apply] at h
    exact h.symm
  -- Step 3: every second-variable coordinate slice vanishes, by separation
  -- on `A`.
  have hcoord : ∀ j, coordSlice c j x = 0 := by
    intro j
    refine eq_zero_of_forall_state_inner_eq_zero _ fun φ ξ ξ' => ?_
    have h1 := coord_sliceRight c j (vecFunctional φ.gnsRep ξ ξ') x
    rw [hslice φ ξ ξ'] at h1
    simp only [map_zero] at h1
    have h2 := h1.symm
    rw [vecFunctional_apply] at h2
    exact h2
  -- Step 4: all coordinate slices vanish, so `x = 0`.
  exact eq_zero_of_forall_coordSlice_eq_zero c hcoord

/-! ## The minimal norm is a C⋆-norm -/

/-- The minimal tensor norm is a C⋆-seminorm: the supremum recipe applied to
the family of GNS pair representations. -/
theorem isCStarSeminorm_minTensorNorm :
    IsCStarSeminorm (minTensorNorm (A := A) (B := B)) :=
  isCStarSeminorm_iSup_starRep inferInstance gnsPairRep
    bddAbove_spatialNorm_gnsRep

/-- **The minimal tensor norm is a C⋆-norm**: definiteness is joint
faithfulness of the GNS pair family. -/
theorem isCStarNorm_minTensorNorm :
    IsCStarNorm (minTensorNorm (A := A) (B := B)) where
  isCStarSeminorm := isCStarSeminorm_minTensorNorm
  eq_zero x hx := by
    refine eq_zero_of_forall_spatialHom_gnsRep_eq_zero fun φ ψ => ?_
    have h1 : spatialNorm φ.gnsRep ψ.gnsRep x ≤ minTensorNorm x :=
      le_ciSup (bddAbove_spatialNorm_gnsRep x) ((φ, ψ) : State A × State B)
    rw [hx] at h1
    have h2 : spatialNorm φ.gnsRep ψ.gnsRep x = 0 :=
      le_antisymm h1 (norm_nonneg _)
    rw [spatialNorm_apply] at h2
    ext ξ
    have hξ : ‖spatialHom φ.gnsRep ψ.gnsRep x ξ‖ ≤ 0 := by
      calc ‖spatialHom φ.gnsRep ψ.gnsRep x ξ‖
          ≤ ‖spatialHom φ.gnsRep ψ.gnsRep x‖ * ‖ξ‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = 0 := by rw [h2, zero_mul]
    simpa using norm_le_zero_iff.mp hξ

/-- **The minimal tensor norm is a cross norm on the nose**:
`‖a ⊗ₜ b‖_min = ‖a‖ * ‖b‖`.  The upper bound is contractivity of every GNS
representation; the lower bound is attained at the pair of norm-attaining
states of `a` and `b`. -/
theorem minTensorNorm_tmul (a : A) (b : B) :
    minTensorNorm (a ⊗ₜ[ℂ] b) = ‖a‖ * ‖b‖ := by
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun p => ?_
    show spatialNorm p.1.gnsRep p.2.gnsRep (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖
    rw [spatialNorm_tmul]
    exact mul_le_mul (p.1.norm_gnsRep_apply_le a)
      (p.2.norm_gnsRep_apply_le b) (norm_nonneg _) (norm_nonneg a)
  · obtain ⟨φ, hφ⟩ := exists_state_norm_le_gnsRep a
    obtain ⟨ψ, hψ⟩ := exists_state_norm_le_gnsRep b
    have h1 : ‖a‖ * ‖b‖ ≤ spatialNorm φ.gnsRep ψ.gnsRep (a ⊗ₜ[ℂ] b) := by
      rw [spatialNorm_tmul]
      exact mul_le_mul hφ hψ (norm_nonneg b) (norm_nonneg _)
    exact h1.trans
      (le_ciSup (bddAbove_spatialNorm_gnsRep _) ((φ, ψ) : State A × State B))

/-! ## The object: `A ⊗_min B` -/

variable (A B) in
/-- The algebraic tensor product retagged with the canonical minimal
C⋆-norm. -/
abbrev MinPreTensor : Type (max u v) :=
  WithCStarNorm (isCStarNorm_minTensorNorm (A := A) (B := B))

variable (A B) in
/-- **The minimal tensor product `A ⊗_min B`**: the completion of the
algebraic tensor product in the canonical minimal C⋆-norm.  Unlike
`SpatialTensorProduct` it is indexed by no choice of representations: the
norm is the supremum over all pairs of states. -/
def MinTensorProduct : Type (max u v) :=
  UniformSpace.Completion (MinPreTensor A B)

noncomputable instance instCStarAlgebraMinTensorProduct :
    CStarAlgebra (MinTensorProduct A B) :=
  completionCStarAlgebraOfIsCStarNorm isCStarNorm_minTensorNorm

variable (A B) in
/-- The canonical ⋆-algebra homomorphism from the algebraic tensor product
into `A ⊗_min B`. -/
noncomputable def minTensorIn :
    (A ⊗[ℂ] B) →⋆ₐ[ℂ] MinTensorProduct A B :=
  (CStarCompletion.coeStarAlgHom (MinPreTensor A B)).comp
    (WithCStarNorm.retagStarAlgHom isCStarNorm_minTensorNorm)

/-- The canonical embedding computes the minimal norm. -/
theorem norm_minTensorIn (x : A ⊗[ℂ] B) :
    ‖minTensorIn A B x‖ = minTensorNorm x :=
  UniformSpace.Completion.norm_coe _

/-- **The cross-norm inside `A ⊗_min B`**: `‖a ⊗ₜ b‖ = ‖a‖ * ‖b‖`.  In
particular `a ↦ a ⊗ₜ 1` and `b ↦ 1 ⊗ₜ b` are isometric, so both factors sit
inside the minimal tensor product with their own norms. -/
theorem norm_minTensorIn_tmul (a : A) (b : B) :
    ‖minTensorIn A B (a ⊗ₜ[ℂ] b)‖ = ‖a‖ * ‖b‖ := by
  rw [norm_minTensorIn, minTensorNorm_tmul]

/-- The canonical embedding is injective. -/
theorem minTensorIn_injective :
    Function.Injective (minTensorIn A B) := by
  intro x y hxy
  have hz : ‖minTensorIn A B (x - y)‖ = 0 := by
    rw [map_sub, hxy, sub_self, norm_zero]
  rw [norm_minTensorIn] at hz
  exact sub_eq_zero.mp (isCStarNorm_minTensorNorm.eq_zero _ hz)

/-- The algebraic tensor product is dense in `A ⊗_min B`. -/
theorem denseRange_minTensorIn :
    DenseRange (minTensorIn A B) :=
  UniformSpace.Completion.denseRange_coe.comp
    (WithCStarNorm.retagStarAlgHom_surjective
      isCStarNorm_minTensorNorm).denseRange
    (UniformSpace.Completion.continuous_coe _)

end CStarTensor
end GroupApproximation
