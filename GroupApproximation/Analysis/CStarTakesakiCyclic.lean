import GroupApproximation.Analysis.CStarTakesakiMinLe
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The cyclic half of Takesaki's identification: one leg at a time

## What this module proves

For a unital C⋆-algebra `A`, *any* ⋆-representation `π` of `A` on a
**complete** Hilbert space `H`, and any ⋆-representation `ρ` of a complex
⋆-algebra `B`:

`spatialNorm π ρ x ≤ leftGnsSup ρ x  :=  ⨆ φ : State A, spatialNorm φ.gnsRep ρ x`.

This is the geometric half of Takesaki's identification: an arbitrary first
leg is dominated by the supremum over GNS first legs.  Classically this is
the decomposition of a representation into cyclic pieces; here the
decomposition is an induction on the number of elementary tensors:

1. **Vector states** (`stateOfVector`): a unit vector of a ⋆-representation
   on a complete space induces a state, because the representation is
   automatically contractive there (`StarRep.toStarAlgHom`, the bridge from
   the adjoint relation to a genuine ⋆-homomorphism into `B(H)`).
2. **Coefficient bound** (`quadratic_coeffVector_le`): at a coefficient
   vector `Σⱼ π(aⱼ)ζ ⊗ ηⱼ` with `‖ζ‖ = 1`, the quadratic form at `x⋆x`
   is exactly the corresponding quadratic form of the *GNS pair of the
   vector state* --- both compute `re φ_ζ(leftSlice ρ a η (x⋆x))` --- so it
   is bounded by `(leftGnsSup ρ x)² ‖w‖²`.  No comparison isometry between
   `H` and the GNS space is ever constructed: the slice element is the
   common value.
3. **Cyclic subspaces** (`quadratic_cyclic_le`): the set `{π(a)ζ : a ∈ A}`
   is already a submodule (the range of `cyclicMap π ζ`), so vectors with
   components in its closure satisfy the same bound by continuity.
4. **Induction** (`quadratic_le_leftGnsSup`): split the components along
   the orthogonal projection onto the closed cyclic subspace of the first
   component; the projected part is (3), the complement has one fewer
   nonzero component, and the two parts are orthogonal under every
   `spatialHom` value because the cyclic subspace and its complement are
   invariant (the adjoint relation again).

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  Combined with the
flip symmetry and the hard half (`CStarTakesakiMinLe`), this yields the full
identification in `CStarTakesakiIdentification.lean`.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped InnerProductSpace TensorProduct

universe u v w x

/-! ## From the adjoint relation to a ⋆-homomorphism, on a complete space -/

section ToStarAlgHom

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- On a complete space, the adjoint relation names the adjoint. -/
theorem IsAdjoint.eq_adjoint {T S : H →L[ℂ] H} (h : IsAdjoint T S) :
    S = ContinuousLinearMap.adjoint T := by
  ext y
  refine ext_inner_left (𝕜 := ℂ) fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (h v y).symm

/-- A ⋆-representation on a complete space is a ⋆-homomorphism into `B(H)`:
the adjoint relation supplies `map_star`. -/
noncomputable def StarRep.toStarAlgHom (π : StarRep A H) :
    A →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  { π.hom with
    map_star' := fun a => by
      show π.hom (star a) = star (π.hom a)
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact (π.isAdjoint_star a).eq_adjoint }

@[simp] theorem StarRep.toStarAlgHom_apply (π : StarRep A H) (a : A) :
    π.toStarAlgHom a = π.hom a := rfl

end ToStarAlgHom

section Contractive

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A ⋆-representation of a C⋆-algebra on a complete space is contractive:
it is a ⋆-homomorphism into the C⋆-algebra `B(H)`. -/
theorem StarRep.norm_hom_apply_le (π : StarRep A H) (a : A) :
    ‖π.hom a‖ ≤ ‖a‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le π.toStarAlgHom a
  simpa using h

/-- The vector state of a unit vector under a ⋆-representation on a
complete space. -/
noncomputable def stateOfVector (π : StarRep A H) (ζ : H) (hζ : ‖ζ‖ = 1) :
    State A where
  toCLM := LinearMap.mkContinuous (vecFunctional π ζ ζ) 1 fun a => by
    rw [one_mul, vecFunctional_apply]
    calc ‖⟪ζ, π.hom a ζ⟫_ℂ‖
        ≤ ‖ζ‖ * ‖π.hom a ζ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ζ‖ * (‖π.hom a‖ * ‖ζ‖) := by
          gcongr
          exact (π.hom a).le_opNorm ζ
      _ = ‖π.hom a‖ := by rw [hζ]; ring
      _ ≤ ‖a‖ := π.norm_hom_apply_le a
  map_one := by
    show vecFunctional π ζ ζ 1 = 1
    rw [vecFunctional_apply, map_one, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hζ]
    norm_num
  norm_le := LinearMap.mkContinuous_norm_le _ zero_le_one _

@[simp] theorem stateOfVector_apply (π : StarRep A H) (ζ : H)
    (hζ : ‖ζ‖ = 1) (a : A) :
    (stateOfVector π ζ hζ).toCLM a = ⟪ζ, π.hom a ζ⟫_ℂ := rfl

end Contractive

/-! ## The one-sided GNS supremum -/

section LeftSup

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (A) in
/-- The supremum, over states of the first factor, of the spatial norms of
the GNS-first-leg pairs. -/
noncomputable def leftGnsSup (ρ : StarRep B K) (x : A ⊗[ℂ] B) : ℝ :=
  ⨆ φ : State A, spatialNorm φ.gnsRep ρ x

theorem bddAbove_spatialNorm_gnsRep_left (ρ : StarRep B K) (x : A ⊗[ℂ] B) :
    BddAbove (Set.range fun φ : State A => spatialNorm φ.gnsRep ρ x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      rintro r ⟨φ, rfl⟩
      exact le_of_eq (spatialNorm_isCStarSeminorm _ _).map_zero
  | tmul a b =>
      refine ⟨‖a‖ * ‖ρ.hom b‖, ?_⟩
      rintro r ⟨φ, rfl⟩
      show spatialNorm φ.gnsRep ρ (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖ρ.hom b‖
      rw [spatialNorm_tmul]
      exact mul_le_mul_of_nonneg_right (φ.norm_gnsRep_apply_le a)
        (norm_nonneg _)
  | add y z hy hz =>
      obtain ⟨Cy, hCy⟩ := hy
      obtain ⟨Cz, hCz⟩ := hz
      refine ⟨Cy + Cz, ?_⟩
      rintro r ⟨φ, rfl⟩
      have h1 : spatialNorm φ.gnsRep ρ (y + z)
          ≤ spatialNorm φ.gnsRep ρ y + spatialNorm φ.gnsRep ρ z :=
        (spatialNorm_isCStarSeminorm _ _).add_le y z
      exact h1.trans (add_le_add (hCy ⟨φ, rfl⟩) (hCz ⟨φ, rfl⟩))

theorem spatialNorm_gnsRep_le_leftGnsSup (ρ : StarRep B K) (x : A ⊗[ℂ] B)
    (φ : State A) : spatialNorm φ.gnsRep ρ x ≤ leftGnsSup A ρ x :=
  le_ciSup (bddAbove_spatialNorm_gnsRep_left ρ x) φ

theorem leftGnsSup_nonneg (ρ : StarRep B K) (x : A ⊗[ℂ] B) :
    0 ≤ leftGnsSup A ρ x :=
  le_trans ((spatialNorm_isCStarSeminorm _ _).nonneg x)
    (spatialNorm_gnsRep_le_leftGnsSup ρ x (Classical.arbitrary _))

end LeftSup

/-! ## The coefficient bound through the vector state -/

section CoefficientBound

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **The coefficient bound**: at a coefficient vector of a unit vector,
the quadratic form at `x⋆x` is bounded through the GNS pair of the vector
state --- both sides compute on the same slice element. -/
theorem quadratic_coeffVector_le (π : StarRep A H) (ρ : StarRep B K)
    {ζ : H} (hζ : ‖ζ‖ = 1) (x : A ⊗[ℂ] B) {n : ℕ} (a : Fin n → A)
    (η : Fin n → K) :
    (⟪coeffVector π ζ a η,
        spatialHom π ρ (star x * x) (coeffVector π ζ a η)⟫_ℂ).re
      ≤ (leftGnsSup A ρ x) ^ 2
        * (⟪coeffVector π ζ a η, coeffVector π ζ a η⟫_ℂ).re := by
  set φ := stateOfVector π ζ hζ with hφ
  set z₁ := leftSlice ρ a η (1 : A ⊗[ℂ] B) with hz₁
  set z₂ := leftSlice ρ a η (star x * x) with hz₂
  have q1 : ⟪coeffVector π ζ a η,
      spatialHom π ρ (star x * x) (coeffVector π ζ a η)⟫_ℂ
      = φ.toCLM z₂ := by
    rw [inner_coeffVector_spatialHom π ρ a η ζ (star x * x), ← hz₂]
    exact (stateOfVector_apply π ζ hζ z₂).symm
  have q2 : ⟪coeffVector π ζ a η, coeffVector π ζ a η⟫_ℂ = φ.toCLM z₁ := by
    rw [inner_coeffVector_self π ρ a η ζ, ← hz₁]
    exact (stateOfVector_apply π ζ hζ z₁).symm
  have g1 : ⟪coeffVector φ.gnsRep φ.gnsVector a η,
      spatialHom φ.gnsRep ρ (star x * x)
        (coeffVector φ.gnsRep φ.gnsVector a η)⟫_ℂ = φ.toCLM z₂ := by
    rw [inner_coeffVector_spatialHom φ.gnsRep ρ a η φ.gnsVector
      (star x * x), ← hz₂]
    exact inner_gnsVector_gnsRep φ z₂
  have g2 : ⟪coeffVector φ.gnsRep φ.gnsVector a η,
      coeffVector φ.gnsRep φ.gnsVector a η⟫_ℂ = φ.toCLM z₁ := by
    rw [inner_coeffVector_self φ.gnsRep ρ a η φ.gnsVector, ← hz₁]
    exact inner_gnsVector_gnsRep φ z₁
  have g3 : (φ.toCLM z₂).re
      = ‖spatialHom φ.gnsRep ρ x (coeffVector φ.gnsRep φ.gnsVector a η)‖ ^ 2 := by
    rw [← g1, inner_spatialHom_star_mul_self]
    exact re_inner_self (spatialHom φ.gnsRep ρ x (coeffVector φ.gnsRep φ.gnsVector a η))
  have g4 : (φ.toCLM z₁).re
      = ‖coeffVector φ.gnsRep φ.gnsVector a η‖ ^ 2 := by
    rw [← g2]
    exact re_inner_self (coeffVector φ.gnsRep φ.gnsVector a η)
  have hM : spatialNorm φ.gnsRep ρ x ≤ leftGnsSup A ρ x :=
    spatialNorm_gnsRep_le_leftGnsSup ρ x φ
  have hb : ‖spatialHom φ.gnsRep ρ x
      (coeffVector φ.gnsRep φ.gnsVector a η)‖
      ≤ leftGnsSup A ρ x * ‖coeffVector φ.gnsRep φ.gnsVector a η‖ := by
    have h1 := (spatialHom φ.gnsRep ρ x).le_opNorm
      (coeffVector φ.gnsRep φ.gnsVector a η)
    have h2 : ‖spatialHom φ.gnsRep ρ x‖ ≤ leftGnsSup A ρ x := by
      rw [← spatialNorm_apply]
      exact hM
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  rw [q1, q2, g3, g4]
  nlinarith [hb, norm_nonneg (spatialHom φ.gnsRep ρ x
      (coeffVector φ.gnsRep φ.gnsVector a η)),
    norm_nonneg (coeffVector φ.gnsRep φ.gnsVector a η),
    leftGnsSup_nonneg (A := A) ρ x]

end CoefficientBound

/-! ## Cyclic subspaces -/

section Cyclic

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The orbit map of a vector under a ⋆-representation, as a linear map;
its range is the algebraic cyclic subspace. -/
noncomputable def cyclicMap (π : StarRep A H) (ζ : H) : A →ₗ[ℂ] H where
  toFun a := π.hom a ζ
  map_add' a b := by rw [map_add, add_apply]
  map_smul' c a := by
    rw [map_smul, smul_apply, RingHom.id_apply]

omit [Nontrivial A] [CompleteSpace H] in
@[simp] theorem cyclicMap_apply (π : StarRep A H) (ζ : H) (a : A) :
    cyclicMap π ζ a = π.hom a ζ := rfl

/-- The elementary-tensor insertion `v ↦ v ⊗ η`, as a continuous linear
map. -/
noncomputable def tmulLeftL (η : K) : H →L[ℂ] (H ⊗[ℂ] K) :=
  LinearMap.mkContinuous ((TensorProduct.mk ℂ H K).flip η) ‖η‖ fun v => by
    rw [LinearMap.flip_apply, TensorProduct.mk_apply,
      TensorProduct.norm_tmul, mul_comm]

omit [CompleteSpace H] in
@[simp] theorem tmulLeftL_apply (η : K) (v : H) :
    tmulLeftL η v = v ⊗ₜ[ℂ] η := rfl

/-- **The cyclic bound**: vectors whose components lie in the closed cyclic
subspace of a nonzero vector satisfy the coefficient bound, by continuity
from the algebraic cyclic subspace, where they are coefficient vectors of
the normalized cyclic vector. -/
theorem quadratic_cyclic_le (π : StarRep A H) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) {ζ : H} (hζ0 : ζ ≠ 0) {m : ℕ} (v : Fin m → H)
    (η : Fin m → K)
    (hv : ∀ i, v i ∈ (LinearMap.range (cyclicMap π ζ)).topologicalClosure) :
    (⟪∑ i : Fin m, v i ⊗ₜ[ℂ] η i,
        spatialHom π ρ (star x * x) (∑ i : Fin m, v i ⊗ₜ[ℂ] η i)⟫_ℂ).re
      ≤ (leftGnsSup A ρ x) ^ 2
        * (⟪∑ i : Fin m, v i ⊗ₜ[ℂ] η i,
            ∑ i : Fin m, v i ⊗ₜ[ℂ] η i⟫_ℂ).re := by
  classical
  set ζh : H := ((‖ζ‖⁻¹ : ℝ) : ℂ) • ζ with hζh
  have hζhn : ‖ζh‖ = 1 := by
    rw [hζh, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ζ)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hζ0)]
  -- the continuous vector assembly
  have hWcont : Continuous fun u : Fin m → H =>
      ∑ i : Fin m, u i ⊗ₜ[ℂ] η i := by
    have he : (fun u : Fin m → H => ∑ i : Fin m, u i ⊗ₜ[ℂ] η i)
        = fun u => ∑ i : Fin m, tmulLeftL (η i) (u i) := rfl
    rw [he]
    exact continuous_finsetSum _ fun i _ =>
      (tmulLeftL (η i)).continuous.comp (continuous_apply i)
  -- the bound set is closed
  have hclosed : IsClosed {u : Fin m → H |
      (⟪∑ i : Fin m, u i ⊗ₜ[ℂ] η i,
          spatialHom π ρ (star x * x)
            (∑ i : Fin m, u i ⊗ₜ[ℂ] η i)⟫_ℂ).re
        ≤ (leftGnsSup A ρ x) ^ 2
          * (⟪∑ i : Fin m, u i ⊗ₜ[ℂ] η i,
              ∑ i : Fin m, u i ⊗ₜ[ℂ] η i⟫_ℂ).re} := by
    refine isClosed_le ?_ ?_
    · exact Complex.continuous_re.comp
        (hWcont.inner ((spatialHom π ρ (star x * x)).continuous.comp hWcont))
    · exact continuous_const.mul
        (Complex.continuous_re.comp (hWcont.inner hWcont))
  -- the algebraic cyclic subspace satisfies the bound
  have hbase : (Set.univ : Set (Fin m)).pi
      (fun _ => ((LinearMap.range (cyclicMap π ζ)) : Set H))
      ⊆ {u : Fin m → H |
        (⟪∑ i : Fin m, u i ⊗ₜ[ℂ] η i,
            spatialHom π ρ (star x * x)
              (∑ i : Fin m, u i ⊗ₜ[ℂ] η i)⟫_ℂ).re
          ≤ (leftGnsSup A ρ x) ^ 2
            * (⟪∑ i : Fin m, u i ⊗ₜ[ℂ] η i,
                ∑ i : Fin m, u i ⊗ₜ[ℂ] η i⟫_ℂ).re} := by
    intro u hu
    have hu' : ∀ i, u i ∈ LinearMap.range (cyclicMap π ζ) := by
      intro i
      exact Set.mem_pi.mp hu i (Set.mem_univ i)
    choose b hb using fun i => LinearMap.mem_range.mp (hu' i)
    -- rescale the witnesses to the unit cyclic vector
    have hcomp : ∀ i, π.hom (((‖ζ‖ : ℝ) : ℂ) • b i) ζh = u i := by
      intro i
      have h1 : π.hom (((‖ζ‖ : ℝ) : ℂ) • b i) ζh
          = ((‖ζ‖ : ℝ) : ℂ) • (π.hom (b i)) ζh := by
        have h0 : π.hom (((‖ζ‖ : ℝ) : ℂ) • b i)
            = ((‖ζ‖ : ℝ) : ℂ) • π.hom (b i) := map_smul π.hom _ _
        rw [h0]
        rfl
      rw [h1, hζh, (π.hom (b i)).map_smul, smul_smul, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hζ0), Complex.ofReal_one,
        one_smul]
      exact hb i
    have hWeq : (∑ i : Fin m, u i ⊗ₜ[ℂ] η i)
        = coeffVector π ζh (fun i => ((‖ζ‖ : ℝ) : ℂ) • b i) η := by
      simp only [coeffVector]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomp i]
    show (⟪∑ i : Fin m, u i ⊗ₜ[ℂ] η i,
        spatialHom π ρ (star x * x)
          (∑ i : Fin m, u i ⊗ₜ[ℂ] η i)⟫_ℂ).re
      ≤ (leftGnsSup A ρ x) ^ 2
        * (⟪∑ i : Fin m, u i ⊗ₜ[ℂ] η i,
            ∑ i : Fin m, u i ⊗ₜ[ℂ] η i⟫_ℂ).re
    rw [hWeq]
    exact quadratic_coeffVector_le π ρ hζhn x _ η
  -- the components lie in the closure of the product
  have hvmem : v ∈ closure ((Set.univ : Set (Fin m)).pi
      (fun _ => ((LinearMap.range (cyclicMap π ζ)) : Set H))) := by
    rw [closure_pi_set]
    rw [Set.mem_pi]
    intro i _
    have h2 : v i ∈ ((LinearMap.range (cyclicMap π ζ)).topologicalClosure :
        Set H) := hv i
    rwa [Submodule.topologicalClosure_coe] at h2
  exact closure_minimal hbase hclosed hvmem

end Cyclic

/-! ## Orthogonality under the product representation -/

section Orthogonal

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

omit [StarModule ℂ A] in
/-- An invariant subspace has invariant orthogonal complement, through the
adjoint relation. -/
theorem mem_orthogonal_hom {π : StarRep A H} {C : Submodule ℂ H}
    (hInv : ∀ (a : A) (v : H), v ∈ C → π.hom a v ∈ C) (a : A) (v : H)
    (hv : v ∈ Cᗮ) : π.hom a v ∈ Cᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← inner_conj_symm u (π.hom a v)]
  have h2 : ⟪π.hom a v, u⟫_ℂ = ⟪v, π.hom (star a) u⟫_ℂ :=
    π.isAdjoint_star a v u
  have h3 : ⟪v, π.hom (star a) u⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (hInv (star a) u hu) hv
  rw [h2, h3, map_zero]

omit [StarModule ℂ A] [StarModule ℂ B] in
/-- Vectors from an invariant subspace and its complement are orthogonal
under every value of the product representation, with the invariant leg on
the left. -/
theorem inner_sum_spatialHom_orthogonal_right (π : StarRep A H)
    (ρ : StarRep B K) {C : Submodule ℂ H}
    (hInv : ∀ (a : A) (v : H), v ∈ C → π.hom a v ∈ C)
    {m₁ m₂ : ℕ} {p : Fin m₁ → H} {ηp : Fin m₁ → K} {q : Fin m₂ → H}
    {ηq : Fin m₂ → K} (hp : ∀ i, p i ∈ C) (hq : ∀ j, q j ∈ Cᗮ)
    (y : A ⊗[ℂ] B) :
    ⟪∑ i : Fin m₁, p i ⊗ₜ[ℂ] ηp i,
      spatialHom π ρ y (∑ j : Fin m₂, q j ⊗ₜ[ℂ] ηq j)⟫_ℂ = 0 := by
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, zero_apply, inner_zero_right]
  | tmul c d =>
      rw [spatialHom_tmul, map_sum, sum_inner]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [inner_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
      have hz : ⟪p i, π.hom c (q j)⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (hp i)
          (mem_orthogonal_hom hInv c (q j) (hq j))
      rw [hz, zero_mul]
  | add y z hy hz =>
      rw [map_add, add_apply, inner_add_right, hy, hz,
        add_zero]

omit [StarModule ℂ A] [StarModule ℂ B] in
/-- The mirrored orthogonality, with the complement leg on the left. -/
theorem inner_sum_spatialHom_orthogonal_left (π : StarRep A H)
    (ρ : StarRep B K) {C : Submodule ℂ H}
    (hInv : ∀ (a : A) (v : H), v ∈ C → π.hom a v ∈ C)
    {m₁ m₂ : ℕ} {p : Fin m₁ → H} {ηp : Fin m₁ → K} {q : Fin m₂ → H}
    {ηq : Fin m₂ → K} (hp : ∀ i, p i ∈ C) (hq : ∀ j, q j ∈ Cᗮ)
    (y : A ⊗[ℂ] B) :
    ⟪∑ j : Fin m₂, q j ⊗ₜ[ℂ] ηq j,
      spatialHom π ρ y (∑ i : Fin m₁, p i ⊗ₜ[ℂ] ηp i)⟫_ℂ = 0 := by
  induction y using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, zero_apply, inner_zero_right]
  | tmul c d =>
      rw [spatialHom_tmul, map_sum, sum_inner]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [TensorProduct.mapL_tmul, TensorProduct.inner_tmul]
      have hz : ⟪q j, π.hom c (p i)⟫_ℂ = 0 :=
        Submodule.inner_left_of_mem_orthogonal (hInv c (p i) (hp i)) (hq j)
      rw [hz, zero_mul]
  | add y z hy hz =>
      rw [map_add, add_apply, inner_add_right, hy, hz,
        add_zero]

end Orthogonal

/-! ## The induction, and the one-leg domination -/

section MainInduction

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {K : Type x} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **The quadratic form of any first leg is dominated by the one-sided GNS
supremum**, by induction on the number of elementary tensors: split along
the orthogonal projection onto the closed cyclic subspace of the first
component. -/
theorem quadratic_le_leftGnsSup (π : StarRep A H) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) :
    ∀ (m : ℕ) (ξ : Fin m → H) (η : Fin m → K),
      (⟪∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i,
          spatialHom π ρ (star x * x)
            (∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i)⟫_ℂ).re
        ≤ (leftGnsSup A ρ x) ^ 2
          * (⟪∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i,
              ∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i⟫_ℂ).re := by
  intro m
  induction m with
  | zero =>
      intro ξ η
      simp
  | succ n ih =>
      intro ξ η
      by_cases hz : ξ 0 = 0
      · rw [Fin.sum_univ_succ, hz, TensorProduct.zero_tmul, zero_add]
        exact ih (fun i => ξ i.succ) (fun i => η i.succ)
      · set C₀ := LinearMap.range (cyclicMap π (ξ 0)) with hC₀
        set C := C₀.topologicalClosure with hC
        -- invariance of the closed cyclic subspace
        have hInv : ∀ (a : A) (v' : H), v' ∈ C → π.hom a v' ∈ C := by
          intro a v' hv'
          have h1 : v' ∈ closure (C₀ : Set H) := by
            rw [hC] at hv'
            exact hv'
          have h3 : (π.hom a) '' (C₀ : Set H) ⊆ (C₀ : Set H) := by
            rintro _ ⟨u', hu', rfl⟩
            obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hu'
            have he : π.hom a (cyclicMap π (ξ 0) b)
                = cyclicMap π (ξ 0) (a * b) := by
              show π.hom a (π.hom b (ξ 0)) = π.hom (a * b) (ξ 0)
              rw [map_mul, mul_eq_comp, ContinuousLinearMap.comp_apply]
            rw [he]
            exact LinearMap.mem_range.mpr ⟨a * b, rfl⟩
          have h2 : π.hom a v' ∈ closure ((π.hom a) '' (C₀ : Set H)) :=
            image_closure_subset_closure_image (π.hom a).continuous
              (Set.mem_image_of_mem _ h1)
          have h4 : π.hom a v' ∈ closure (C₀ : Set H) :=
            closure_mono h3 h2
          rw [hC]
          exact h4
        -- membership facts
        have hpm : ∀ i : Fin (n + 1), C.starProjection (ξ i) ∈ C :=
          fun i => C.starProjection_apply_mem (ξ i)
        have hqm : ∀ i : Fin (n + 1),
            ξ i - C.starProjection (ξ i) ∈ Cᗮ :=
          fun i => Submodule.sub_starProjection_mem_orthogonal (K := C) (ξ i)
        have hq0 : ξ 0 - C.starProjection (ξ 0) = 0 := by
          have hmem : ξ 0 ∈ C := by
            apply Submodule.le_topologicalClosure
            exact LinearMap.mem_range.mpr ⟨1, by
              show π.hom 1 (ξ 0) = ξ 0
              rw [map_one, one_apply_eq_self]⟩
          rw [Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]
        -- the split
        have hsplit : (∑ i : Fin (n + 1), ξ i ⊗ₜ[ℂ] η i)
            = (∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i)
              + ∑ i : Fin (n + 1), (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← TensorProduct.add_tmul]
          congr 1
          abel
        -- the two bounds
        have h1 : (⟪∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i,
            spatialHom π ρ (star x * x)
              (∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i)⟫_ℂ).re
            ≤ (leftGnsSup A ρ x) ^ 2
              * (⟪∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i,
                  ∑ i : Fin (n + 1),
                    C.starProjection (ξ i) ⊗ₜ[ℂ] η i⟫_ℂ).re := by
          refine quadratic_cyclic_le π ρ x hz _ η fun i => ?_
          rw [← hC]
          exact hpm i
        have h2 : (⟪∑ i : Fin (n + 1),
              (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i,
            spatialHom π ρ (star x * x)
              (∑ i : Fin (n + 1),
                (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i)⟫_ℂ).re
            ≤ (leftGnsSup A ρ x) ^ 2
              * (⟪∑ i : Fin (n + 1),
                    (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i,
                  ∑ i : Fin (n + 1),
                    (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i⟫_ℂ).re := by
          have e : (∑ i : Fin (n + 1),
              (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i)
              = ∑ i : Fin n,
                  (ξ i.succ - C.starProjection (ξ i.succ)) ⊗ₜ[ℂ] η i.succ := by
            rw [Fin.sum_univ_succ, hq0, TensorProduct.zero_tmul, zero_add]
          rw [e]
          exact ih (fun i => ξ i.succ - C.starProjection (ξ i.succ))
            (fun i => η i.succ)
        -- cross terms vanish
        have hcrossL := inner_sum_spatialHom_orthogonal_right π ρ hInv
          (ηp := η) (ηq := η) hpm hqm
        have hcrossR := inner_sum_spatialHom_orthogonal_left π ρ hInv
          (ηp := η) (ηq := η) hpm hqm
        have hS : ⟪(∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i)
              + ∑ i : Fin (n + 1),
                (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i,
            spatialHom π ρ (star x * x)
              ((∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i)
                + ∑ i : Fin (n + 1),
                  (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i)⟫_ℂ
            = ⟪∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i,
                spatialHom π ρ (star x * x)
                  (∑ i : Fin (n + 1),
                    C.starProjection (ξ i) ⊗ₜ[ℂ] η i)⟫_ℂ
              + ⟪∑ i : Fin (n + 1),
                    (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i,
                  spatialHom π ρ (star x * x)
                    (∑ i : Fin (n + 1),
                      (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i)⟫_ℂ := by
          rw [map_add, inner_add_left, inner_add_right, inner_add_right,
            hcrossL (star x * x), hcrossR (star x * x)]
          ring
        have hone : ⟪(∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i)
              + ∑ i : Fin (n + 1),
                (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i,
            (∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i)
              + ∑ i : Fin (n + 1),
                (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i⟫_ℂ
            = ⟪∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i,
                ∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i⟫_ℂ
              + ⟪∑ i : Fin (n + 1),
                    (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i,
                  ∑ i : Fin (n + 1),
                    (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i⟫_ℂ := by
          have hcL : ⟪∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i,
              ∑ i : Fin (n + 1),
                (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i⟫_ℂ = 0 := by
            have h := hcrossL (1 : A ⊗[ℂ] B)
            rwa [map_one, one_apply_eq_self] at h
          have hcR : ⟪∑ i : Fin (n + 1),
                (ξ i - C.starProjection (ξ i)) ⊗ₜ[ℂ] η i,
              ∑ i : Fin (n + 1), C.starProjection (ξ i) ⊗ₜ[ℂ] η i⟫_ℂ = 0 := by
            have h := hcrossR (1 : A ⊗[ℂ] B)
            rwa [map_one, one_apply_eq_self] at h
          rw [inner_add_left, inner_add_right, inner_add_right, hcL, hcR]
          ring
        rw [hsplit, hS, hone, Complex.add_re, Complex.add_re, mul_add]
        exact add_le_add h1 h2

/-- **One-leg domination**: any first leg on a complete space is dominated
by the one-sided GNS supremum. -/
theorem spatialNorm_le_leftGnsSup (π : StarRep A H) (ρ : StarRep B K)
    (x : A ⊗[ℂ] B) : spatialNorm π ρ x ≤ leftGnsSup A ρ x := by
  rw [spatialNorm_apply]
  refine ContinuousLinearMap.opNorm_le_bound _ (leftGnsSup_nonneg ρ x)
    fun w => ?_
  obtain ⟨m, ξ, η, rfl⟩ := exists_fin_sum_tmul w
  have h := quadratic_le_leftGnsSup π ρ x m ξ η
  have e1 : (⟪∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i,
      spatialHom π ρ (star x * x) (∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i)⟫_ℂ).re
      = ‖spatialHom π ρ x (∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i)‖ ^ 2 := by
    rw [inner_spatialHom_star_mul_self]
    exact re_inner_self (spatialHom π ρ x (∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i))
  have e2 : (⟪∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i,
      ∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i⟫_ℂ).re
      = ‖∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i‖ ^ 2 :=
    re_inner_self (∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i)
  rw [e1, e2] at h
  have hnn : 0 ≤ ‖spatialHom π ρ x (∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i)‖ :=
    norm_nonneg _
  have hnn2 : 0 ≤ leftGnsSup A ρ x * ‖∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i‖ :=
    mul_nonneg (leftGnsSup_nonneg ρ x) (norm_nonneg _)
  refine (sq_le_sq₀ hnn hnn2).mp ?_
  have hsq : (leftGnsSup A ρ x * ‖∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i‖) ^ 2
      = (leftGnsSup A ρ x) ^ 2 * ‖∑ i : Fin m, ξ i ⊗ₜ[ℂ] η i‖ ^ 2 := by
    ring
  rw [hsq]
  exact h

end MainInduction

end CStarTensor
end GroupApproximation
