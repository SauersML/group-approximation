import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.CrossedProductOperators

/-!
# The regular covariant pair and the integrated form

Lane TWWUCT-A (work order WO-TWWUCT-A), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).  Following Brown--Ozawa §4.1 and
Williams, §2.3 and §7.2, a representation `ρ : A → B(H)` induces the regular
covariant pair `(π̃, λ)` on `ℓ²(G, H)`:

* `diag G ρ : A →⋆ₙₐ[ℂ] B(ℓ²(G, H))`, `(π̃(a) ξ)(s) = ρ(s⁻¹ · a)(ξ s)`;
* covariance `λ_g π̃(b) = π̃(g · b) λ_g` (`shift_mul_diag`);
* `gen ρ a g = π̃(a) λ_g`, with `gen a g * gen b h = gen (a (g · b)) (g h)` and
  `(gen a g)⋆ = gen (g⁻¹ · a⋆) g⁻¹`;
* the integrated form `integrate ρ : (G →₀ A) →ₗ[ℂ] B(ℓ²(G, H))`, whose range is
  closed under products and adjoints.
-/

namespace GroupApproximation.Full.TWWUCT.CrossedProduct

open scoped InnerProductSpace

universe u v w

noncomputable section

variable {G : Type u} [Group G]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type v} [NonUnitalCStarAlgebra A] [GCStarAlgebra G A]
variable (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

omit [CompleteSpace H] in
theorem norm_shift_le (g : G) : ‖shift (H := H) g‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le ((shiftLinear g).isometryOfInner _)

variable (G) in
/-- **The twisted diagonal representation** `π̃ : A → B(ℓ²(G, H))`,
`(π̃(a) ξ)(s) = ρ(s⁻¹ · a)(ξ s)` (Brown--Ozawa §4.1).  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
def diag : A →⋆ₙₐ[ℂ] (L2 G H →L[ℂ] L2 G H) where
  toFun := diagOp ρ
  map_smul' c a := by
    refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => ?_)
    change ρ (GCStarAlgebra.act (A := A) s⁻¹ (c • a)) (ξ s) =
      c • ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s)
    rw [map_smul, map_smul, ContinuousLinearMap.smul_apply]
  map_zero' := by
    refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => ?_)
    change ρ (GCStarAlgebra.act (A := A) s⁻¹ (0 : A)) (ξ s) = 0
    rw [map_zero, map_zero, ContinuousLinearMap.zero_apply]
  map_add' a b := by
    refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => ?_)
    change ρ (GCStarAlgebra.act (A := A) s⁻¹ (a + b)) (ξ s) =
      ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s) + ρ (GCStarAlgebra.act (A := A) s⁻¹ b) (ξ s)
    rw [map_add, map_add, ContinuousLinearMap.add_apply]
  map_mul' a b := by
    refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => ?_)
    change ρ (GCStarAlgebra.act (A := A) s⁻¹ (a * b)) (ξ s) =
      ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ρ (GCStarAlgebra.act (A := A) s⁻¹ b) (ξ s))
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply]
  map_star' a := by
    change diagOp (G := G) ρ (star a) = star (diagOp (G := G) ρ a)
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    intro ξ η
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun s => ?_
    rw [diagOp_apply, diagOp_apply, map_star, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]

theorem diag_apply (a : A) (ξ : L2 G H) (s : G) :
    diag G ρ a ξ s = ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s) :=
  rfl

/-- **Covariance** of the regular pair: `λ_g π̃(b) = π̃(g · b) λ_g`
(Brown--Ozawa §4.1).  `non_mf_group_notes.tex`, `thm:fixed-radical-membership`. -/
theorem shift_mul_diag (g : G) (b : A) :
    shift (H := H) g * diag G ρ b = diag G ρ (GCStarAlgebra.act (A := A) g b) * shift g := by
  refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => ?_)
  change ρ (GCStarAlgebra.act (A := A) (g⁻¹ * s)⁻¹ b) (ξ (g⁻¹ * s)) =
    ρ (GCStarAlgebra.act (A := A) s⁻¹ (GCStarAlgebra.act (A := A) g b)) (ξ (g⁻¹ * s))
  rw [← GCStarAlgebra.act_mul_apply, mul_inv_rev, inv_inv]

/-! ## Generators and the integrated form -/

/-- The operator `π̃(a) λ_g`, the image of `a δ_g`. -/
def gen (a : A) (g : G) : L2 G H →L[ℂ] L2 G H :=
  diag G ρ a * shift g

theorem gen_apply (a : A) (g : G) (ξ : L2 G H) (s : G) :
    gen ρ a g ξ s = ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ (g⁻¹ * s)) :=
  rfl

theorem gen_mul_gen (a b : A) (g h : G) :
    gen ρ a g * gen ρ b h = gen ρ (a * GCStarAlgebra.act (A := A) g b) (g * h) := by
  change diag G ρ a * shift g * (diag G ρ b * shift h) =
    diag G ρ (a * GCStarAlgebra.act (A := A) g b) * shift (g * h)
  rw [mul_assoc (diag G ρ a), ← mul_assoc (shift g) (diag G ρ b), shift_mul_diag,
    mul_assoc (diag G ρ (GCStarAlgebra.act (A := A) g b)), shift_mul_shift,
    ← mul_assoc (diag G ρ a), ← map_mul (diag G ρ)]

theorem star_gen (a : A) (g : G) :
    star (gen ρ a g) = gen ρ (GCStarAlgebra.act (A := A) g⁻¹ (star a)) g⁻¹ := by
  change star (diag G ρ a * shift g) =
    diag G ρ (GCStarAlgebra.act (A := A) g⁻¹ (star a)) * shift g⁻¹
  rw [star_mul, star_shift, ← map_star (diag G ρ), shift_mul_diag]

theorem norm_gen_le (a : A) (g : G) : ‖gen ρ a g‖ ≤ ‖a‖ :=
  calc ‖gen ρ a g‖ ≤ ‖diag G ρ a‖ * ‖shift (H := H) g‖ := norm_mul_le (diag G ρ a) (shift g)
    _ ≤ ‖diag G ρ a‖ * 1 := mul_le_mul_of_nonneg_left (norm_shift_le g) (norm_nonneg _)
    _ = ‖diag G ρ a‖ := mul_one _
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le (diag G ρ) a

/-- `a ↦ π̃(a) λ_g`, as a linear map. -/
def genLinear (g : G) : A →ₗ[ℂ] (L2 G H →L[ℂ] L2 G H) where
  toFun a := gen ρ a g
  map_add' a b := by
    change diag G ρ (a + b) * shift g = diag G ρ a * shift g + diag G ρ b * shift g
    rw [map_add, add_mul]
  map_smul' c a := by
    change diag G ρ (c • a) * shift g = c • (diag G ρ a * shift g)
    rw [map_smul, smul_mul_assoc]

/-- **The integrated form** of the regular covariant pair,
`∑ a_g δ_g ↦ ∑ π̃(a_g) λ_g` (Williams, Prop. 2.23; Brown--Ozawa §4.1).
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
def integrate : (G →₀ A) →ₗ[ℂ] (L2 G H →L[ℂ] L2 G H) :=
  Finsupp.lsum ℂ (genLinear ρ)

theorem integrate_apply (x : G →₀ A) : integrate ρ x = x.sum fun g a => gen ρ a g :=
  rfl

theorem integrate_single (g : G) (a : A) : integrate ρ (Finsupp.single g a) = gen ρ a g :=
  Finsupp.lsum_single ℂ (genLinear ρ) g a

theorem integrate_mul_mem (x y : G →₀ A) :
    integrate ρ x * integrate ρ y ∈ LinearMap.range (integrate ρ) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, zero_mul]
    exact zero_mem _
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, add_mul]
    exact add_mem h₁ h₂
  | single g a =>
    induction y using Finsupp.induction_linear with
    | zero =>
      rw [map_zero, mul_zero]
      exact zero_mem _
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, mul_add]
      exact add_mem h₁ h₂
    | single h b =>
      rw [integrate_single, integrate_single, gen_mul_gen, ← integrate_single]
      exact LinearMap.mem_range_self _ _

theorem star_integrate_mem (x : G →₀ A) :
    star (integrate ρ x) ∈ LinearMap.range (integrate ρ) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, star_zero]
    exact zero_mem _
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, star_add]
    exact add_mem h₁ h₂
  | single g a =>
    rw [integrate_single, star_gen, ← integrate_single]
    exact LinearMap.mem_range_self _ _

end

end GroupApproximation.Full.TWWUCT.CrossedProduct
