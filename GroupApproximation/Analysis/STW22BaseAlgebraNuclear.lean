import GroupApproximation.Analysis.CStarNuclearProduct
import GroupApproximation.Analysis.STW22BaseAlgebraUnitization
import GroupApproximation.Analysis.STW22RealProjectiveBlockNuclear

/-!
# Nuclearity of the concrete scalar-tail base algebra

The first `N` coordinates together with the limiting scalar form a nuclear
finite product.  The associated scalar-tail truncations are completely
positive contractions and converge in norm to every base element.  Composing
these truncations with finite-dimensional approximations of the finite product
gives a direct CPAP for the actual `BaseAlgebra`.
-/

namespace GroupApproximation
namespace STW22BaseAlgebraNuclear

open Filter Topology PolarLiftingGeneralCStar
open CStarExactness CStarC0DirectSum
open UniformTracialSequenceCompletion STW22ActualTraceSpaces
open STW22BaseAlgebraUnitization

noncomputable section

variable (D : ℕ → Type) [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- The scalar quotient of a minimal unitization. -/
def unitizationScalarStarAlgHom (A : Type) [NonUnitalCStarAlgebra A] :
    Unitization ℂ A →⋆ₐ[ℂ] ℂ where
  toFun x := x.fst
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- The canonical limiting scalar of a base element. -/
def baseScalarStarAlgHom : BaseAlgebra D →⋆ₐ[ℂ] ℂ :=
  (unitizationScalarStarAlgHom (C0DirectSum D)).comp
    (unitizationEquivBase D).symm.toStarAlgHom

/-- The finite scalar-and-coordinate product used at truncation length `N`. -/
abbrev BasePrefix (N : ℕ) := ℂ × (∀ i : Fin N, D i.1)

/-- Read the limiting scalar and the first `N` coordinates. -/
def basePrefixDown (N : ℕ) : BaseAlgebra D →⋆ₐ[ℂ] BasePrefix D N where
  toFun x := (baseScalarStarAlgHom D x, fun i ↦ x.1 i.1)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  commutes' c := by
    apply Prod.ext
    · exact (baseScalarStarAlgHom D).commutes c
    · funext i
      rfl
  map_star' x := by
    apply Prod.ext
    · exact map_star (baseScalarStarAlgHom D) x
    · funext i
      rfl

private theorem finiteAssembly_apply (N : ℕ)
    (a : ∀ i : Fin N, D i.1) (n : ℕ) :
    ((finiteAssembly D N a : C0DirectSum D) : BoundedCStarSequence D) n =
      if h : n < N then a ⟨n, h⟩ else 0 := by
  classical
  let ev : C0DirectSum D →+ D n :=
    { toFun := fun x ↦ x.1 n
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  rw [finiteAssembly]
  change ev (∑ i : Fin N, summandInclusion D i.1 (a i)) = _
  rw [map_sum]
  by_cases hn : n < N
  · rw [dif_pos hn, Finset.sum_eq_single ⟨n, hn⟩]
    · exact summandInclusion_apply_self D n (a ⟨n, hn⟩)
    · intro i hi hin
      exact summandInclusion_apply_ne (D := D) (n := i.1) (m := n)
        (fun h ↦ hin (Fin.ext h.symm)) (a i)
    · simp
  · rw [dif_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    exact summandInclusion_apply_ne (D := D) (n := i.1) (m := n)
      (by intro h; apply hn; omega) (a i)

/-- Assemble a finite prefix and continue it by the specified scalar. -/
def basePrefixUpElement (N : ℕ) (z : BasePrefix D N) : BaseAlgebra D :=
  unitizationToBase D
    (Unitization.inl z.1 +
      (finiteAssembly D N
        (fun i ↦ z.2 i - algebraMap ℂ (D i.1) z.1) :
          Unitization ℂ (C0DirectSum D)))

@[simp] theorem basePrefixUpElement_apply (N : ℕ) (z : BasePrefix D N)
    (n : ℕ) :
    (basePrefixUpElement D N z).1 n =
      if h : n < N then z.2 ⟨n, h⟩ else algebraMap ℂ (D n) z.1 := by
  classical
  simp only [basePrefixUpElement, map_add, unitizationToBase_inl,
    unitizationToBase_inr]
  change algebraMap ℂ (D n) z.1 +
      ((finiteAssembly D N (fun i ↦ z.2 i - algebraMap ℂ (D i.1) z.1) :
        C0DirectSum D) : BoundedCStarSequence D) n = _
  rw [finiteAssembly_apply]
  split_ifs <;> simp

/-- Put a finite prefix back into the base algebra with a scalar tail. -/
def basePrefixUp (N : ℕ) : BasePrefix D N →⋆ₐ[ℂ] BaseAlgebra D where
  toFun := basePrefixUpElement D N
  map_zero' := by
    apply Subtype.ext
    apply lp.ext
    funext n
    simp [basePrefixUpElement_apply]
  map_one' := by
    apply Subtype.ext
    apply lp.ext
    funext n
    simp [basePrefixUpElement_apply]
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext n
    by_cases hn : n < N <;> simp [basePrefixUpElement_apply, hn]
  map_mul' x y := by
    apply Subtype.ext
    apply lp.ext
    funext n
    by_cases hn : n < N <;> simp [basePrefixUpElement_apply, hn, map_mul]
  commutes' c := by
    apply Subtype.ext
    apply lp.ext
    funext n
    rw [basePrefixUpElement_apply]
    by_cases hn : n < N
    · rw [dif_pos hn]
      rfl
    · rw [dif_neg hn]
      rfl
  map_star' x := by
    apply Subtype.ext
    apply lp.ext
    funext n
    rw [basePrefixUpElement_apply,
      show ((star (basePrefixUpElement D N x)).1 n) =
        star ((basePrefixUpElement D N x).1 n) by rfl,
      basePrefixUpElement_apply]
    by_cases hn : n < N <;>
      simp [hn, Algebra.algebraMap_eq_smul_one]

private theorem unitizationToBase_apply_coordinate
    (z : Unitization ℂ (C0DirectSum D)) (n : ℕ) :
    (unitizationToBase D z).1 n =
      algebraMap ℂ (D n) z.fst + z.snd.1 n := by
  induction z using Unitization.ind with
  | inl_add_inr c b =>
      rw [map_add, unitizationToBase_inl, unitizationToBase_inr]
      change algebraMap ℂ (D n) c + b.1 n =
        algebraMap ℂ (D n) (Unitization.inl c +
          (b : Unitization ℂ (C0DirectSum D))).fst +
        (Unitization.inl c + (b : Unitization ℂ (C0DirectSum D))).snd.1 n
      simp

/-- The canonical scalar really is a norm-convergent scalar tail. -/
theorem tendsto_norm_sub_baseScalar (x : BaseAlgebra D) :
    Tendsto (fun n ↦ ‖x.1 n - algebraMap ℂ (D n) (baseScalarStarAlgHom D x)‖)
      atTop (nhds 0) := by
  let z := (unitizationEquivBase D).symm x
  have hx : unitizationEquivBase D z = x :=
    (unitizationEquivBase D).apply_symm_apply x
  have hscalar : baseScalarStarAlgHom D x = z.fst := rfl
  rw [hscalar]
  apply z.snd.2.congr'
  filter_upwards with n
  have hcoord := congrArg (fun y : BaseAlgebra D ↦ y.1 n) hx
  change (unitizationToBase D z).1 n = x.1 n at hcoord
  rw [unitizationToBase_apply_coordinate] at hcoord
  rw [← hcoord]
  simp

/-- Scalar truncation with the canonical tail scalar, bundled in the base. -/
def canonicalBaseTruncation (x : BaseAlgebra D) (N : ℕ) : BaseAlgebra D :=
  ⟨scalarTruncation x.1 (baseScalarStarAlgHom D x) N,
    (mem_baseAlgebra_iff _).2
      (scalarTruncation_mem_unitizedC0Sum x.1 (baseScalarStarAlgHom D x) N)⟩

@[simp] theorem canonicalBaseTruncation_apply (x : BaseAlgebra D) (N n : ℕ) :
    (canonicalBaseTruncation D x N).1 n =
      if n ≤ N then x.1 n else algebraMap ℂ (D n) (baseScalarStarAlgHom D x) :=
  scalarTruncation_apply x.1 (baseScalarStarAlgHom D x) N n

/-- Reading and rewriting a prefix is exactly scalar truncation. -/
theorem basePrefixUp_down (x : BaseAlgebra D) (N : ℕ) :
    basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x) =
      canonicalBaseTruncation D x N := by
  change basePrefixUpElement D (N + 1) (basePrefixDown D (N + 1) x) = _
  apply Subtype.ext
  apply lp.ext
  funext n
  rw [basePrefixUpElement_apply, canonicalBaseTruncation_apply]
  by_cases hn : n ≤ N
  · rw [dif_pos (Nat.lt_succ_iff.2 hn), if_pos hn]
    rfl
  · rw [dif_neg (by simpa only [Nat.lt_succ_iff] using hn), if_neg hn]
    rfl

/-- Canonical scalar truncations converge in operator norm. -/
theorem tendsto_canonicalBaseTruncation (x : BaseAlgebra D) :
    Tendsto (canonicalBaseTruncation D x) atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  have htail := tendsto_norm_sub_baseScalar D x
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨N₀, hN₀⟩ := htail (eps / 2) hhalf
  refine ⟨N₀, fun N hNN₀ ↦ ?_⟩
  rw [dist_eq_norm]
  change ‖(scalarTruncation x.1 (baseScalarStarAlgHom D x) N - x.1 :
    BoundedCStarSequence D)‖ < eps
  rw [lp.norm_eq_ciSup]
  apply lt_of_le_of_lt (ciSup_le fun n ↦ ?_) (half_lt_self heps)
  by_cases hn : n ≤ N
  · rw [show (scalarTruncation x.1 (baseScalarStarAlgHom D x) N - x.1) n = 0 by
      simp [scalarTruncation_apply, hn]]
    simpa using hhalf.le
  · have hNn : N ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hN₀n : N₀ ≤ n := hNN₀.trans hNn
    have h := hN₀ n hN₀n
    rw [Real.dist_eq, sub_zero, abs_norm] at h
    rw [show (scalarTruncation x.1 (baseScalarStarAlgHom D x) N - x.1) n =
        -(x.1 n - algebraMap ℂ (D n) (baseScalarStarAlgHom D x)) by
      simp [scalarTruncation_apply, hn], norm_neg]
    exact h.le

/-- Scalar-prefix factorizations converge in norm to every base element. -/
theorem tendsto_basePrefixUp_down (x : BaseAlgebra D) :
    Tendsto (fun N ↦ basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x))
      atTop (nhds x) := by
  apply (tendsto_canonicalBaseTruncation D x).congr'
  exact Eventually.of_forall fun N ↦ (basePrefixUp_down D x N).symm

/-- The actual scalar-plus-`c₀` base is nuclear whenever every block is
nuclear. -/
theorem isNuclearCStarAlgebra_baseAlgebra
    (hD : ∀ n, IsNuclearCStarAlgebra (D n)) :
    IsNuclearCStarAlgebra (BaseAlgebra D) := by
  classical
  intro F eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  have hconv : ∀ x ∈ F, ∀ᶠ N in atTop,
      ‖basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x) - x‖ < eps / 2 := by
    intro x hx
    exact (Metric.tendsto_nhds.mp (tendsto_basePrefixUp_down D x)
      (eps / 2) hhalf).mono fun N hN ↦ by
        simpa [dist_eq_norm] using hN
  have hall : ∀ᶠ N in atTop, ∀ x ∈ F,
      ‖basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x) - x‖ < eps / 2 :=
    (Finset.eventually_all F).2 fun x hx ↦ hconv x hx
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hall
  let N := N₀
  have hN : ∀ x ∈ F,
      ‖basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x) - x‖ < eps / 2 :=
    fun x hx ↦ hN₀ N le_rfl x hx
  have hPrefix : IsNuclearCStarAlgebra (BasePrefix D (N + 1)) :=
    (isNuclearCStarAlgebra_of_finiteDimensional ℂ).prod
      (isNuclearCStarAlgebra_piFin (N + 1) (fun i ↦ D i.1) (fun i ↦ hD i.1))
  obtain ⟨E, alpha, beta, halpha, hbeta, halphaC, hbetaC, happ⟩ :=
    hPrefix (F.image (basePrefixDown D (N + 1))) (eps / 2) hhalf
  let down : BaseAlgebra D →ₗ[ℂ] E :=
    alpha.comp (basePrefixDown D (N + 1)).toLinearMap
  let up : E →ₗ[ℂ] BaseAlgebra D :=
    (basePrefixUp D (N + 1)).toLinearMap.comp beta
  refine ⟨E, down, up,
    halpha.comp (isCompletelyPositive_of_starAlgHom
      (basePrefixDown D (N + 1)).toNonUnitalStarAlgHom),
    (isCompletelyPositive_of_starAlgHom
      (basePrefixUp D (N + 1)).toNonUnitalStarAlgHom).comp hbeta,
    ?_, ?_, ?_⟩
  · intro x
    exact (halphaC _).trans (NonUnitalStarAlgHom.norm_apply_le
      (basePrefixDown D (N + 1)) x)
  · intro e
    exact (NonUnitalStarAlgHom.norm_apply_le
      (basePrefixUp D (N + 1)) (beta e)).trans (hbetaC e)
  · intro x hx
    apply le_of_lt
    calc
      ‖up (down x) - x‖ ≤
          ‖basePrefixUp D (N + 1)
              (beta (alpha (basePrefixDown D (N + 1) x))) -
            basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x)‖ +
          ‖basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x) - x‖ := by
            dsimp only [up, down]
            rw [show up (down x) - x =
                (up (down x) - basePrefixUp D (N + 1)
                  (basePrefixDown D (N + 1) x)) +
                (basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x) - x) by
              abel]
            exact norm_add_le _ _
      _ ≤ ‖beta (alpha (basePrefixDown D (N + 1) x)) -
              basePrefixDown D (N + 1) x‖ +
            ‖basePrefixUp D (N + 1) (basePrefixDown D (N + 1) x) - x‖ := by
          gcongr
          rw [← map_sub]
          exact NonUnitalStarAlgHom.norm_apply_le (basePrefixUp D (N + 1)) _
      _ < eps / 2 + eps / 2 := add_lt_add_of_le_of_lt
          (happ _ (Finset.mem_image_of_mem _ hx)) (hN x hx)
      _ = eps := by ring

/-! ## Concrete antipodal specialization -/

/-- Every scalar-plus-`c₀` base made from real-projective blocks is nuclear. -/
theorem isNuclearCStarAlgebra_baseAlgebra_realProjectiveBlocks
    (d s : ℕ → ℕ) :
    IsNuclearCStarAlgebra
      (BaseAlgebra (fun n ↦ STW22.RealProjectiveBlock (d n) (s n))) :=
  isNuclearCStarAlgebra_baseAlgebra _
    (fun n ↦ STW22.isNuclearCStarAlgebra_realProjectiveBlock (d n) (s n))

/-- The literal base algebra of the antipodal counterexample is nuclear. -/
theorem isNuclearCStarAlgebra_baseAlgebra_antipodalCounterexampleBlock :
    IsNuclearCStarAlgebra (BaseAlgebra STW22.AntipodalCounterexampleBlock) :=
  isNuclearCStarAlgebra_baseAlgebra_realProjectiveBlocks
    STW22.antipodalBlockDimension STW22.antipodalBlockSize

end

end STW22BaseAlgebraNuclear
end GroupApproximation
