import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.Stab

/-!
# Reindexing isometries and inner conjugations of `𝒦 ⊗ B`

For an injective map `α : ℕ → ℕ` we build the isometry `V_α` of `ℓ²(ℕ, H_B)` with
`V_α (δ_i ⊗ v) = δ_{α i} ⊗ v`, as the adjoint of the contraction `(P_α x)_k = x_{α k}`:

* `Stab.reindex B α hα = V_α`, with `V_α⋆ V_α = 1` and
  `V_α (e_{ij} ⊗ T) = e_{α(i) j} ⊗ T`, `(e_{ij} ⊗ T) V_α⋆ = e_{i α(j)} ⊗ T`;
* `Stab.IsLeftMul U`: `U (𝒦 ⊗ B) ⊆ 𝒦 ⊗ B`; it suffices to check this on the generators
  `e_{ij} ⊗ π(b)` (`isLeftMul_of_generators`), and then also `(𝒦 ⊗ B) U⋆ ⊆ 𝒦 ⊗ B`;
* `Stab.conj U hU hUU : 𝒦 ⊗ B → 𝒦 ⊗ B`, `x ↦ U x U⋆`, a `⋆`-homomorphism for an isometry `U`
  (`U⋆ U = 1`) with `IsLeftMul U`, continuous in `U` (`continuous_conj_apply`);
* `Stab.adReindex B α hα = conj V_α`, with `e_{ij} ⊗ b ↦ e_{α(i) α(j)} ⊗ b`.

These are the inner endomorphisms of the stabilization used in Cuntz's proof that
`[𝒦 ⊗ D, 𝒦 ⊗ E] ≅ [D, 𝒦 ⊗ E]` (J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987)
31--51, §1; Blackadar, *K-Theory for Operator Algebras*, 17.8).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C2a, work order WO-TWWKK-C2a).
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

open scoped ENNReal

namespace Stab

variable {B : Type u} [NonUnitalCStarAlgebra B]

/-! ## The reindexing contraction `P_α` and the isometry `V_α = P_α⋆` -/

theorem memℓp_comp_reindex {α : ℕ → ℕ} (hα : Function.Injective α) (x : Space B) :
    Memℓp (fun k : ℕ => x (α k)) 2 := by
  apply memℓp_gen
  exact ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp x)).comp_injective hα

variable (B) in
/-- The reindexing map `(P_α x)_k = x_{α k}` on `ℓ²(ℕ, H_B)`, as a linear map. -/
def pullbackLinear (α : ℕ → ℕ) (hα : Function.Injective α) : Space B →ₗ[ℂ] Space B where
  toFun x := ⟨fun k => x (α k), memℓp_comp_reindex hα x⟩
  map_add' x y := by
    apply lp.ext
    funext k
    change (⇑(x + y)) (α k) = x (α k) + y (α k)
    rw [lp.coeFn_add, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext k
    change (⇑(c • x)) (α k) = c • x (α k)
    rw [lp.coeFn_smul, Pi.smul_apply]

variable {α : ℕ → ℕ} {hα : Function.Injective α}

theorem norm_pullbackLinear_le (x : Space B) : ‖pullbackLinear B α hα x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  refine lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (norm_nonneg x) ?_
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x]
  exact tsum_comp_le_tsum_of_inj ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp x))
    (fun i => Real.rpow_nonneg (norm_nonneg (x i)) _) hα

variable (B) in
/-- **The reindexing contraction** `P_α : ℓ²(ℕ, H_B) → ℓ²(ℕ, H_B)`, `(P_α x)_k = x_{α k}`. -/
def pullback (α : ℕ → ℕ) (hα : Function.Injective α) : Ambient B :=
  (pullbackLinear B α hα).mkContinuous 1 norm_pullbackLinear_le

theorem pullback_apply (x : Space B) (k : ℕ) : pullback B α hα x k = x (α k) :=
  rfl

theorem pullback_single (k : ℕ) (v : RepSpace B) :
    pullback B α hα (lp.single 2 (α k) v) = lp.single 2 k v := by
  apply lp.ext
  funext m
  change (lp.single 2 (α k) v : Space B) (α m) = (lp.single 2 k v : Space B) m
  by_cases h : m = k
  · subst h
    rw [lp.single_apply_self, lp.single_apply_self]
  · rw [lp.single_apply_ne 2 (α k) v (hα.ne h), lp.single_apply_ne 2 k v h]

variable (B) in
/-- **The reindexing isometry** `V_α = P_α⋆`, `δ_i ⊗ v ↦ δ_{α i} ⊗ v`. -/
def reindex (α : ℕ → ℕ) (hα : Function.Injective α) : Ambient B :=
  star (pullback B α hα)

theorem star_reindex : star (reindex B α hα) = pullback B α hα :=
  star_star _

theorem reindex_single (i : ℕ) (v : RepSpace B) :
    reindex B α hα (lp.single 2 i v) = lp.single 2 (α i) v := by
  refine ext_inner_right ℂ fun y => ?_
  calc inner ℂ (reindex B α hα (lp.single 2 i v)) y
      = inner ℂ (lp.single 2 i v : Space B) (pullback B α hα y) := by
        rw [reindex, ContinuousLinearMap.star_eq_adjoint]
        exact ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = inner ℂ v (y (α i)) := lp.inner_single_left i v _
    _ = inner ℂ (lp.single 2 (α i) v : Space B) y := (lp.inner_single_left (α i) v y).symm

theorem reindex_comp_inj (i : ℕ) : reindex B α hα ∘L inj B i = inj B (α i) :=
  ContinuousLinearMap.ext fun v => reindex_single i v

/-- **`V_α` is an isometry**: `V_α⋆ V_α = 1`. -/
theorem star_reindex_mul_reindex : star (reindex B α hα) * reindex B α hα = 1 := by
  rw [star_reindex]
  refine ContinuousLinearMap.ext fun x => lp.ext (funext fun k => ?_)
  refine ext_inner_left ℂ fun v => ?_
  change inner ℂ v ((reindex B α hα x : Space B) (α k)) = inner ℂ v (x k)
  calc inner ℂ v ((reindex B α hα x : Space B) (α k))
      = inner ℂ (lp.single 2 (α k) v : Space B) (reindex B α hα x) :=
        (lp.inner_single_left (α k) v _).symm
    _ = inner ℂ (pullback B α hα (lp.single 2 (α k) v)) x := by
        rw [reindex, ContinuousLinearMap.star_eq_adjoint]
        exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = inner ℂ (lp.single 2 k v : Space B) x := by rw [pullback_single]
    _ = inner ℂ v (x k) := lp.inner_single_left k v x

/-- `V_α (e_{ij} ⊗ T) = e_{α(i) j} ⊗ T`. -/
theorem reindex_mul_matUnit (i j : ℕ) (T : RepSpace B →L[ℂ] RepSpace B) :
    reindex B α hα * matUnit B i j T = matUnit B (α i) j T := by
  refine ContinuousLinearMap.ext fun x => ?_
  change reindex B α hα (lp.single 2 i (T (x j))) = lp.single 2 (α i) (T (x j))
  exact reindex_single i (T (x j))

/-- `(e_{ij} ⊗ T) V_α⋆ = e_{i α(j)} ⊗ T`. -/
theorem matUnit_mul_star_reindex (i j : ℕ) (T : RepSpace B →L[ℂ] RepSpace B) :
    matUnit B i j T * star (reindex B α hα) = matUnit B i (α j) T := by
  have h := congrArg star (reindex_mul_matUnit (hα := hα) j i (star T))
  rw [star_mul, star_matUnit, star_matUnit, star_star] at h
  exact h

/-! ## Left multipliers of `𝒦 ⊗ B` -/

/-- `U` multiplies `𝒦 ⊗ B` into itself from the left. -/
def IsLeftMul (U : Ambient B) : Prop :=
  ∀ x ∈ closedSubalgebra B, U * x ∈ closedSubalgebra B

theorem IsLeftMul.mul_star_mem {U : Ambient B} (hU : IsLeftMul U) {x : Ambient B}
    (hx : x ∈ closedSubalgebra B) : x * star U ∈ closedSubalgebra B := by
  have h := star_mem (hU (star x) (star_mem hx))
  rwa [star_mul, star_star] at h

theorem IsLeftMul.mul {U V : Ambient B} (hU : IsLeftMul U) (hV : IsLeftMul V) :
    IsLeftMul (U * V) := fun x hx => by
  rw [mul_assoc]
  exact hU _ (hV x hx)

theorem isLeftMul_one : IsLeftMul (1 : Ambient B) := fun x hx => by
  rw [one_mul]
  exact hx

/-- **Left multipliers are detected on generators**: if `U (e_{ij} ⊗ π(b)) ∈ 𝒦 ⊗ B` for all
`i, j, b`, then `U (𝒦 ⊗ B) ⊆ 𝒦 ⊗ B`. -/
theorem isLeftMul_of_generators {U : Ambient B}
    (hU : ∀ (i j : ℕ) (b : B), U * matUnit B i j (rep B b) ∈ closedSubalgebra B) :
    IsLeftMul U := by
  have hfin : ∀ x ∈ finiteMatrices B,
      U * x ∈ closedSubalgebra B ∧ x * star U ∈ closedSubalgebra B := by
    intro x hx
    change x ∈ NonUnitalStarAlgebra.adjoin ℂ (generators B) at hx
    induction hx using NonUnitalStarAlgebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, j, b, rfl⟩ : ∃ (i j : ℕ) (b : B), x = matUnit B i j (rep B b) := hx
      refine ⟨hU i j b, ?_⟩
      have h := star_mem (hU j i (star b))
      rwa [star_mul, map_star, star_matUnit, star_star] at h
    | add x y _ _ hx hy =>
      rw [mul_add, add_mul]
      exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | zero =>
      rw [mul_zero, zero_mul]
      exact ⟨zero_mem _, zero_mem _⟩
    | mul x y hx' hy' hx hy =>
      rw [← mul_assoc U x y, mul_assoc x y (star U)]
      exact ⟨mul_mem hx.1 (finiteMatrices_le_closedSubalgebra hy'),
        mul_mem (finiteMatrices_le_closedSubalgebra hx') hy.2⟩
    | smul c x _ hx =>
      rw [mul_smul_comm, smul_mul_assoc]
      exact ⟨SMulMemClass.smul_mem c hx.1, SMulMemClass.smul_mem c hx.2⟩
    | star x _ hx =>
      refine ⟨?_, ?_⟩
      · have h := star_mem hx.2
        rwa [star_mul, star_star] at h
      · have h := star_mem hx.1
        rwa [star_mul] at h
  intro x hx
  have hx' : x ∈ closure (finiteMatrices B : Set (Ambient B)) := hx
  have hsub : (finiteMatrices B : Set (Ambient B)) ⊆
      (fun y : Ambient B => U * y) ⁻¹' (closedSubalgebra B : Set (Ambient B)) :=
    fun y hy => (hfin y hy).1
  exact closure_minimal hsub ((isClosed_closedSubalgebra B).preimage (continuous_const_mul U)) hx'

theorem isLeftMul_reindex : IsLeftMul (reindex B α hα) :=
  isLeftMul_of_generators fun i j b => by
    rw [reindex_mul_matUnit]
    exact matUnit_rep_mem (α i) j b

/-! ## Conjugation by an isometric left multiplier -/

/-- **Conjugation** `x ↦ U x U⋆` of `𝒦 ⊗ B` by an isometry `U` (`U⋆ U = 1`) multiplying
`𝒦 ⊗ B` into itself. -/
def conj (U : Ambient B) (hU : IsLeftMul U) (hUU : star U * U = 1) :
    Stab B →⋆ₙₐ[ℂ] Stab B where
  toFun x := ⟨U * x * star U, hU.mul_star_mem (hU x x.2)⟩
  map_smul' c x := Subtype.ext <| by
    change U * (c • (x : Ambient B)) * star U = c • (U * x * star U)
    rw [mul_smul_comm, smul_mul_assoc]
  map_zero' := Subtype.ext <| by
    change U * (0 : Ambient B) * star U = 0
    rw [mul_zero, zero_mul]
  map_add' x y := Subtype.ext <| by
    change U * ((x : Ambient B) + y) * star U = U * x * star U + U * y * star U
    rw [mul_add, add_mul]
  map_mul' x y := Subtype.ext <| by
    change U * ((x : Ambient B) * y) * star U = U * x * star U * (U * y * star U)
    rw [show U * (x : Ambient B) * star U * (U * y * star U) =
        U * x * (star U * U) * y * star U by simp only [mul_assoc], hUU, mul_one,
      mul_assoc U (x : Ambient B) y]
  map_star' x := Subtype.ext <| by
    change U * star (x : Ambient B) * star U = star (U * x * star U)
    rw [star_mul, star_mul, star_star, mul_assoc]

theorem coe_conj (U : Ambient B) (hU : IsLeftMul U) (hUU : star U * U = 1) (x : Stab B) :
    (conj U hU hUU x : Ambient B) = U * x * star U :=
  rfl

/-- `t ↦ U_t x U_t⋆` is continuous for a norm-continuous path of isometric left multipliers. -/
theorem continuous_conj_apply {U : ℝ → Ambient B} (hU : Continuous U)
    (hL : ∀ t, IsLeftMul (U t)) (hUU : ∀ t, star (U t) * U t = 1) (x : Stab B) :
    Continuous fun t => conj (U t) (hL t) (hUU t) x :=
  continuous_induced_rng.2
    ((hU.mul continuous_const).mul (continuous_star.comp hU) :
      Continuous fun t => U t * (x : Ambient B) * star (U t))

/-! ## Reindexing conjugations -/

variable (B) in
/-- **The reindexing endomorphism** `Ad V_α : 𝒦 ⊗ B → 𝒦 ⊗ B`,
`e_{ij} ⊗ b ↦ e_{α(i) α(j)} ⊗ b`. -/
def adReindex (α : ℕ → ℕ) (hα : Function.Injective α) : Stab B →⋆ₙₐ[ℂ] Stab B :=
  conj (reindex B α hα) isLeftMul_reindex star_reindex_mul_reindex

theorem coe_adReindex (x : Stab B) :
    (adReindex B α hα x : Ambient B) = reindex B α hα * x * star (reindex B α hα) :=
  rfl

theorem adReindex_single (i j : ℕ) (b : B) :
    adReindex B α hα (single i j b) = single (α i) (α j) b :=
  Subtype.ext <| by
    change reindex B α hα * matUnit B i j (rep B b) * star (reindex B α hα) =
      matUnit B (α i) (α j) (rep B b)
    rw [reindex_mul_matUnit, matUnit_mul_star_reindex]

/-- `V_α x V_β⋆ ∈ 𝒦 ⊗ B` for `x ∈ 𝒦 ⊗ B`. -/
theorem reindex_mul_mul_star_reindex_mem {β : ℕ → ℕ} {hβ : Function.Injective β}
    {x : Ambient B} (hx : x ∈ closedSubalgebra B) :
    reindex B α hα * x * star (reindex B β hβ) ∈ closedSubalgebra B :=
  isLeftMul_reindex.mul_star_mem (isLeftMul_reindex x hx)

theorem reindex_mul_matUnit_mul_star_reindex {β : ℕ → ℕ} {hβ : Function.Injective β}
    (i j : ℕ) (T : RepSpace B →L[ℂ] RepSpace B) :
    reindex B α hα * matUnit B i j T * star (reindex B β hβ) = matUnit B (α i) (β j) T := by
  rw [reindex_mul_matUnit, matUnit_mul_star_reindex]

end Stab

end

end GroupApproximation.Full.TWWKK
