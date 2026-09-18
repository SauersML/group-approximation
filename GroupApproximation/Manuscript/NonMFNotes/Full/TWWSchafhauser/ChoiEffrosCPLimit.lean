import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosCPBasics
import GroupApproximation.Analysis.CStarMatrixFactorization

/-!
# Choi–Effros lifting, point-norm limits of completely positive contractions

Lane `TWWSchafhauser-3a` (work order `WO-TWWCore-3`, piece 3a).

* `isCompletelyPositive_of_tendsto` — a point-norm limit of completely positive
  maps is completely positive: the amplifications converge entrywise, hence in
  the matrix C⋆-norm, and the positive cone of `M_n(B)` is closed;
* `cauchySeq_of_denseSet` — a sequence of contractions that is pointwise Cauchy
  on a dense set is pointwise Cauchy everywhere;
* `exists_cpc_lift_of_cauchy` — if completely positive contractions `ψ_m` are
  pointwise Cauchy on a dense set `S` and `π ∘ ψ_m → φ` on `S`, the pointwise
  limit is a completely positive contractive lift of `φ`.

This is the closure step of Arveson's theorem that point-norm limits of liftable
maps are liftable: W. Arveson, *Notes on extensions of C⋆-algebras*, Duke Math.
J. **44** (1977), 329–355, §2; N. P. Brown, N. Ozawa, *C⋆-algebras and
finite-dimensional approximations*, Lemma C.2 and proof of Theorem C.3.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter Topology

noncomputable section

universe u v w

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- **Point-norm limits of completely positive maps are completely positive.** -/
theorem isCompletelyPositive_of_tendsto {ψ : ℕ → A →ₗ[ℂ] B}
    (hψ : ∀ m, CStarExactness.IsCompletelyPositive (ψ m)) {L : A →ₗ[ℂ] B}
    (hL : ∀ a, Tendsto (fun m ↦ ψ m a) atTop (𝓝 (L a))) :
    CStarExactness.IsCompletelyPositive L := by
  letI : PartialOrder A := CStarAlgebra.spectralOrder A
  letI : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  refine CStarExactness.isCompletelyPositive_of_map_nonneg L fun n M hM ↦ ?_
  have hmat : Tendsto (fun m ↦ (fun i j ↦ ψ m (M i j) : Matrix (Fin n) (Fin n) B)) atTop
      (𝓝 (fun i j ↦ L (M i j) : Matrix (Fin n) (Fin n) B)) :=
    tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ hL (M i j)
  have hcs : Tendsto (fun m ↦ M.map ⇑(ψ m)) atTop (𝓝 (M.map ⇑L)) :=
    (CStarMatrix.ofMatrixL.continuous.tendsto _).comp hmat
  exact CStarAlgebra.isClosed_nonneg.mem_of_tendsto hcs
    (Eventually.of_forall fun m ↦
      CStarExactness.map_nonneg_of_isCompletelyPositive (hψ m) n M hM)

/-- A pointwise Cauchy sequence of linear maps into a Banach space has a linear
pointwise limit. -/
theorem exists_linearMap_tendsto {ψ : ℕ → A →ₗ[ℂ] B}
    (hC : ∀ a, CauchySeq fun m ↦ ψ m a) :
    ∃ L : A →ₗ[ℂ] B, ∀ a, Tendsto (fun m ↦ ψ m a) atTop (𝓝 (L a)) := by
  choose lim hlim using fun a ↦ cauchySeq_tendsto_of_complete (hC a)
  refine ⟨{ toFun := lim, map_add' := fun a b ↦ ?_, map_smul' := fun c a ↦ ?_ }, hlim⟩
  · refine tendsto_nhds_unique (hlim (a + b)) ?_
    exact Tendsto.congr (fun m ↦ (map_add (ψ m) a b).symm) ((hlim a).add (hlim b))
  · refine tendsto_nhds_unique (hlim (c • a)) ?_
    exact Tendsto.congr (fun m ↦ (map_smul (ψ m) c a).symm) ((hlim a).const_smul c)

/-- A sequence of contractions that is pointwise Cauchy on a dense set is
pointwise Cauchy everywhere (an `ε/3` argument). -/
theorem cauchySeq_of_denseSet {ψ : ℕ → A →ₗ[ℂ] B} (hψc : ∀ m a, ‖ψ m a‖ ≤ ‖a‖)
    {S : Set A} (hS : Dense S) (hC : ∀ s ∈ S, CauchySeq fun m ↦ ψ m s) (a : A) :
    CauchySeq fun m ↦ ψ m a := by
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨s, hs, has⟩ := hS.exists_dist_lt a hε3
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hC s hs) (ε / 3) hε3
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hclose : ∀ k, dist (ψ k a) (ψ k s) ≤ dist a s := fun k ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub (ψ k)]
    exact hψc k (a - s)
  have h4 := dist_triangle4 (ψ m a) (ψ m s) (ψ n s) (ψ n a)
  have h1 := hclose m
  have h3 : dist (ψ n s) (ψ n a) ≤ dist a s := by
    rw [dist_comm]
    exact hclose n
  have h2 := hN m hm n hn
  linarith

/-- A pointwise limit of contractions is a contraction. -/
theorem norm_apply_le_of_tendsto {ψ : ℕ → A →ₗ[ℂ] B} (hψc : ∀ m a, ‖ψ m a‖ ≤ ‖a‖)
    {L : A →ₗ[ℂ] B} (hL : ∀ a, Tendsto (fun m ↦ ψ m a) atTop (𝓝 (L a))) (a : A) :
    ‖L a‖ ≤ ‖a‖ :=
  le_of_tendsto' (hL a).norm fun m ↦ hψc m a

/-- **The closure step.**  Completely positive contractions `ψ_m : A → B` that are
pointwise Cauchy on a dense set `S`, with `π ∘ ψ_m → φ` pointwise on `S`,
converge pointwise to a completely positive contractive lift of the contraction
`φ`. -/
theorem exists_cpc_lift_of_cauchy {C : Type w} [CStarAlgebra C] (π : B →⋆ₐ[ℂ] C)
    {φ : A →ₗ[ℂ] C} (hφc : ∀ a, ‖φ a‖ ≤ ‖a‖) {ψ : ℕ → A →ₗ[ℂ] B}
    (hψ : ∀ m, CStarExactness.IsCompletelyPositive (ψ m))
    (hψc : ∀ m a, ‖ψ m a‖ ≤ ‖a‖) {S : Set A} (hS : Dense S)
    (hC : ∀ s ∈ S, CauchySeq fun m ↦ ψ m s)
    (hπ : ∀ s ∈ S, Tendsto (fun m ↦ π (ψ m s)) atTop (𝓝 (φ s))) :
    ∃ L : A →ₗ[ℂ] B, CStarExactness.IsCompletelyPositive L ∧
      (∀ a, ‖L a‖ ≤ ‖a‖) ∧ ∀ a, π (L a) = φ a := by
  obtain ⟨L, hL⟩ := exists_linearMap_tendsto (cauchySeq_of_denseSet hψc hS hC)
  have hLc := norm_apply_le_of_tendsto hψc hL
  have hπcont : Continuous π :=
    AddMonoidHomClass.continuous_of_bound π 1 fun b ↦
      (NonUnitalStarAlgHom.norm_apply_le π b).trans_eq (one_mul _).symm
  have hLcont : Continuous L :=
    AddMonoidHomClass.continuous_of_bound L 1 fun a ↦ (hLc a).trans_eq (one_mul _).symm
  have hφcont : Continuous φ :=
    AddMonoidHomClass.continuous_of_bound φ 1 fun a ↦ (hφc a).trans_eq (one_mul _).symm
  have heq : Set.EqOn (fun a ↦ π (L a)) φ S := fun s hs ↦
    tendsto_nhds_unique ((hπcont.tendsto (L s)).comp (hL s)) (hπ s hs)
  refine ⟨L, isCompletelyPositive_of_tendsto hψ hL, hLc, fun a ↦ ?_⟩
  exact congrFun ((hπcont.comp hLcont).ext_on hS hφcont heq) a

end

end TWWSchafhauser
end Full
end GroupApproximation
