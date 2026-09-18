import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnitalHomotopy
import GroupApproximation.AlgTop.BundleCalculusProjection
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Topology.Instances.Matrix

/-!
# Homotopy invariance of `K₀` for non-unital C⋆-algebras

Lane `TWWSch3d3-1A`, work order `WO-3d3-1A`, for `thm:fixed-radical-membership`
(`non_mf_group_notes.tex`, l.1376--1378). The source is M. Rørdam, F. Larsen, N. Laustsen,
*An introduction to K-theory for C⋆-algebras*: Proposition 2.2.4 (projections at distance `< 1`
are unitarily equivalent), Proposition 2.2.7 (homotopic projections are unitarily equivalent), and
Proposition 3.2.6 / 4.1.4 (homotopy invariance of `K₀`).

* `kZero_mk_eq_of_norm_sub_lt_one`: two projections `p q ∈ M_n(A)` with `‖p - q‖ < 1` have the
  same class in `K₀(A)`, where `A` is a unital C⋆-algebra and the norm is the C⋆-norm of
  `M_n(A)` (RLL 2.2.4). The analytic step is `BundleCalculus.unitaryConj_of_norm_sub_lt_one`;
* `kZero_mk_map_eq_of_path`: if `g : ℝ → (B →⋆ₙ+* A)` is a pointwise continuous path of
  ⋆-homomorphisms into a unital C⋆-algebra, then `[g₀(x)] = [g₁(x)]` for every projection `x`
  over `B`. The path `t ↦ g_t(x)` is a continuous path of projections in `M_n(A)`, so its
  endpoints are Murray--von Neumann equivalent (RLL 2.2.7). That proof covers `[0,1]` by the balls
  of radius `1` from RLL 2.2.4 and uses connectedness (`BundleCalculus.unitaryConj_of_preconnected`);
* `KZeroN.map_eq_of_nhomotopic`: homotopic non-unital ⋆-homomorphisms `J → J'` induce the same
  map `K₀(J) → K₀(J')`. We apply the previous item to the unitized path
  `t ↦ (p t)⁺ : J⁺ → J'⁺`.

The matrix algebra `M_n(A)` is Mathlib's `CStarMatrix (Fin n) (Fin n) A`. It is definitionally
`Matrix (Fin n) (Fin n) A`, and the projection-picture `K₀` of `GroupApproximation.KTheory` is
built on `Matrix`. The two small transfer lemmas `isStarProjection_ofMatrix` and
`murrayVonNeumannEquiv_of_ofMatrix` cross between the two, as term-mode definitional equalities.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

/-! ### Close projections in a unital C⋆-algebra have the same `K₀` class -/

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A projection in `Matrix (Fin n) (Fin n) A` is a projection in the C⋆-algebra
`CStarMatrix (Fin n) (Fin n) A`. -/
theorem isStarProjection_ofMatrix {n : ℕ} {p : Matrix (Fin n) (Fin n) A}
    (hp : IsStarProjection p) :
    IsStarProjection (CStarMatrix.ofMatrix p : CStarMatrix (Fin n) (Fin n) A) :=
  ⟨hp.isIdempotentElem, hp.isSelfAdjoint⟩

/-- Murray--von Neumann equivalence in the C⋆-algebra `CStarMatrix (Fin n) (Fin n) A` is
Murray--von Neumann equivalence of the underlying matrices. -/
theorem murrayVonNeumannEquiv_of_ofMatrix {n : ℕ} {p q : Matrix (Fin n) (Fin n) A}
    (h : MurrayVonNeumannEquiv (CStarMatrix.ofMatrix p : CStarMatrix (Fin n) (Fin n) A)
      (CStarMatrix.ofMatrix q)) :
    MurrayVonNeumannEquiv p q := by
  obtain ⟨v, hv₁, hv₂⟩ := h
  exact ⟨CStarMatrix.ofMatrix.symm v, hv₁, hv₂⟩

/-- **Close projections have the same `K₀` class** (RLL Proposition 2.2.4). If `p q ∈ M_n(A)`
are projections with `‖p - q‖ < 1` in the C⋆-norm of `M_n(A)`, then `[p] = [q]` in `K₀(A)`. -/
theorem kZero_mk_eq_of_norm_sub_lt_one {n : ℕ} {p q : Matrix (Fin n) (Fin n) A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : ‖(CStarMatrix.ofMatrix p - CStarMatrix.ofMatrix q : CStarMatrix (Fin n) (Fin n) A)‖ < 1) :
    KTheory.KZero.mk (⟨n, p, hp⟩ : KTheory.Cycle A) = KTheory.KZero.mk ⟨n, q, hq⟩ :=
  KTheory.KZero.mk_eq_mk_of_rel (KTheory.Cycle.rel_of_step (KTheory.Cycle.Step.mvn
    (murrayVonNeumannEquiv_of_ofMatrix
      (BundleCalculus.murrayVonNeumannEquiv_of_norm_sub_lt_one
        (isStarProjection_ofMatrix hp) (isStarProjection_ofMatrix hq) h))))

/-- **Homotopy invariance on classes of projections** (RLL Proposition 2.2.7). Let
`g : ℝ → (B →⋆ₙ+* A)` be a pointwise continuous path of ⋆-homomorphisms into a unital
C⋆-algebra `A`. Then `g 0` and `g 1` give every projection over `B` the same class in `K₀(A)`. -/
theorem kZero_mk_map_eq_of_path {B : Type*} [NonUnitalSemiring B] [StarRing B]
    {g : ℝ → (B →⋆ₙ+* A)} (hg : ∀ b : B, Continuous fun t : ℝ => g t b)
    (x : KTheory.Cycle B) :
    KTheory.KZero.mk (x.map (g 0)) = KTheory.KZero.mk (x.map (g 1)) := by
  obtain ⟨n, P, hP⟩ := x
  have hc : Continuous fun t : ℝ =>
      (CStarMatrix.ofMatrix (P.map (g t)) : CStarMatrix (Fin n) (Fin n) A) := by
    refine continuous_matrix fun i j => ?_
    exact (hg (P i j)).congr fun _ => rfl
  have hproj : ∀ t : ℝ, IsStarProjection
      (CStarMatrix.ofMatrix (P.map (g t)) : CStarMatrix (Fin n) (Fin n) A) :=
    fun t => isStarProjection_ofMatrix (KTheory.isStarProjection_map (g t) hP)
  have hmvn : MurrayVonNeumannEquiv (P.map (g 0)) (P.map (g 1)) :=
    murrayVonNeumannEquiv_of_ofMatrix
      (BundleCalculus.murrayVonNeumannEquiv_of_path
        (f := fun t : ℝ => (CStarMatrix.ofMatrix (P.map (g t)) : CStarMatrix (Fin n) (Fin n) A))
        hc hproj)
  show KTheory.KZero.mk (⟨n, P.map (g 0), KTheory.isStarProjection_map (g 0) hP⟩ :
      KTheory.Cycle A) =
    KTheory.KZero.mk ⟨n, P.map (g 1), KTheory.isStarProjection_map (g 1) hP⟩
  exact KTheory.KZero.mk_eq_mk_of_rel (KTheory.Cycle.rel_of_step (KTheory.Cycle.Step.mvn hmvn))

/-- **Homotopy invariance of `K₀`** for coefficient maps into a unital C⋆-algebra. -/
theorem kZero_map_eq_of_path {B : Type*} [NonUnitalSemiring B] [StarRing B]
    {g : ℝ → (B →⋆ₙ+* A)} (hg : ∀ b : B, Continuous fun t : ℝ => g t b) :
    KTheory.KZero.map (g 0) = KTheory.KZero.map (g 1) := by
  refine KTheory.KZero.hom_ext fun x => ?_
  rw [KTheory.KZero.map_mk, KTheory.KZero.map_mk]
  exact kZero_mk_map_eq_of_path hg x

end Unital

/-! ### Homotopy invariance of `K₀(J)` -/

section NonUnital

attribute [local instance] unitizationOrder unitizationStarOrderedRing

variable {J J' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']

/-- A pointwise continuous path of non-unital ⋆-homomorphisms `J → J'` induces one map
`K₀(J⁺) → K₀(J'⁺)` along the whole path. -/
theorem kZero_map_starMap_eq_of_path {p : ℝ → (J →⋆ₙₐ[ℂ] J')}
    (hp : ∀ a : J, Continuous fun t : ℝ => p t a) :
    KTheory.KZero.map (starRingHomOf (Unitization.starMap (p 0))) =
      KTheory.KZero.map (starRingHomOf (Unitization.starMap (p 1))) :=
  kZero_map_eq_of_path (A := Unitization ℂ J')
    (g := fun t : ℝ => starRingHomOf (Unitization.starMap (p t)))
    (fun b => (continuous_starMap_apply hp b).congr fun _ => (starRingHomOf_apply _ b).symm)

/-- **Homotopy invariance of `K₀`** (RLL Proposition 4.1.4, non-unital form). Homotopic
non-unital ⋆-homomorphisms induce the same map on `K₀`. -/
theorem KZeroN.map_eq_of_nhomotopic {φ ψ : J →⋆ₙₐ[ℂ] J'} (h : TWWKK.NHomotopic φ ψ) :
    KZeroN.map φ = KZeroN.map ψ := by
  obtain ⟨p, hp, rfl, rfl⟩ := h
  have key := kZero_map_starMap_eq_of_path hp
  refine AddMonoidHom.ext fun x => Subtype.ext ?_
  exact (KZeroN.map_apply_coe (p 0) x).trans
    ((DFunLike.congr_fun key x.1).trans (KZeroN.map_apply_coe (p 1) x).symm)

end NonUnital

end

end TWWSchafhauser
end Full
end GroupApproximation
