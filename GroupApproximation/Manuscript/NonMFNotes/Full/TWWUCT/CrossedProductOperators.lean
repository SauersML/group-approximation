import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.CrossedProductBasic

/-!
# The regular covariant representation on `ℓ²(G, H)`

Lane TWWUCT-A (work order WO-TWWUCT-A), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).  Brown--Ozawa §4.1 (and Williams,
§7.2) build the reduced crossed product from a representation
`ρ : A → B(H)` by letting `A` act on `ℓ²(G, H)` diagonally, twisted by the action,
and `G` act by left translation:

* `shift g`: `(λ_g ξ)(s) = ξ(g⁻¹ s)`, a unitary with `λ_g λ_h = λ_{gh}` and
  `λ_g⋆ = λ_{g⁻¹}`;
* `diag ρ`: `(π̃(a) ξ)(s) = ρ(s⁻¹ · a)(ξ s)`, a `⋆`-homomorphism;
* covariance `λ_g π̃(b) = π̃(g · b) λ_g`;
* `gen ρ a g = π̃(a) λ_g`, with `gen a g · gen b h = gen (a (g · b)) (g h)` and
  `(gen a g)⋆ = gen (g⁻¹ · a⋆) g⁻¹`;
* `integrate ρ : (G →₀ A) →ₗ[ℂ] B(ℓ²(G, H))`, `∑ a_g δ_g ↦ ∑ π̃(a_g) λ_g`, whose
  range is closed under products and adjoints.
-/

namespace GroupApproximation.Full.TWWUCT.CrossedProduct

open scoped InnerProductSpace

universe u v w

noncomputable section

variable {G : Type u} [Group G]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (G H) in
/-- The Hilbert space `ℓ²(G, H)`. -/
abbrev L2 : Type (max u w) := lp (fun _ : G => H) 2

theorem memℓp_comp_mulLeft (g : G) (ξ : L2 G H) :
    Memℓp (fun s : G => ξ ((Equiv.mulLeft g).symm s)) 2 := by
  apply memℓp_gen
  exact (Equiv.summable_iff (Equiv.mulLeft g).symm).2
    ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp ξ))

/-- Left translation on `ℓ²(G, H)`, as a linear map. -/
def shiftLinear (g : G) : L2 G H →ₗ[ℂ] L2 G H where
  toFun ξ := ⟨fun s => ξ ((Equiv.mulLeft g).symm s), memℓp_comp_mulLeft g ξ⟩
  map_add' ξ η := by
    apply lp.ext
    funext s
    change (⇑(ξ + η)) ((Equiv.mulLeft g).symm s) =
      ξ ((Equiv.mulLeft g).symm s) + η ((Equiv.mulLeft g).symm s)
    rw [lp.coeFn_add, Pi.add_apply]
  map_smul' c ξ := by
    apply lp.ext
    funext s
    change (⇑(c • ξ)) ((Equiv.mulLeft g).symm s) = c • ξ ((Equiv.mulLeft g).symm s)
    rw [lp.coeFn_smul, Pi.smul_apply]

/-- **Left translation** `λ_g` on `ℓ²(G, H)` (Brown--Ozawa §4.1). -/
def shift (g : G) : L2 G H →L[ℂ] L2 G H :=
  ((shiftLinear g).isometryOfInner (by
    intro ξ η
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact Equiv.tsum_eq (Equiv.mulLeft g).symm fun s => ⟪ξ s, η s⟫_ℂ)).toContinuousLinearMap

theorem shift_apply (g : G) (ξ : L2 G H) (s : G) : shift g ξ s = ξ (g⁻¹ * s) :=
  rfl

theorem shift_mul_shift (g h : G) : shift (H := H) g * shift h = shift (g * h) := by
  refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => ?_)
  change ξ (h⁻¹ * (g⁻¹ * s)) = ξ ((g * h)⁻¹ * s)
  rw [mul_inv_rev, mul_assoc]

theorem shift_one : shift (H := H) (1 : G) = 1 := by
  refine ContinuousLinearMap.ext fun ξ => lp.ext (funext fun s => ?_)
  change ξ ((1 : G)⁻¹ * s) = ξ s
  rw [inv_one, one_mul]

variable [CompleteSpace H]

theorem star_shift (g : G) : star (shift (H := H) g) = shift g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  calc ∑' s, ⟪(shift g⁻¹ ξ) s, η s⟫_ℂ = ∑' s, ⟪ξ (g * s), η (g⁻¹ * (g * s))⟫_ℂ := by
        refine tsum_congr fun s => ?_
        rw [shift_apply, inv_inv, inv_mul_cancel_left]
    _ = ∑' s, ⟪ξ s, η (g⁻¹ * s)⟫_ℂ :=
        Equiv.tsum_eq (Equiv.mulLeft g) fun t => ⟪ξ t, η (g⁻¹ * t)⟫_ℂ
    _ = ∑' s, ⟪ξ s, (shift g η) s⟫_ℂ := rfl

/-! ## The twisted diagonal representation -/

variable {A : Type v} [NonUnitalCStarAlgebra A] [GCStarAlgebra G A]
variable (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

theorem norm_rep_act_le (a : A) (s : G) :
    ‖ρ (GCStarAlgebra.act (A := A) s⁻¹ a)‖ ≤ ‖a‖ :=
  (NonUnitalStarAlgHom.norm_apply_le ρ _).trans (GCStarAlgebra.norm_act _ a).le

/-- The twisted diagonal action of one element, as a linear map. -/
def diagLinear (a : A) : L2 G H →ₗ[ℂ] L2 G H where
  toFun ξ := ⟨fun s => ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s), by
    refine Memℓp.mono' ((lp.memℓp ξ).const_smul (‖a‖ : ℂ)) fun s => ?_
    calc ‖ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s)‖
        ≤ ‖ρ (GCStarAlgebra.act (A := A) s⁻¹ a)‖ * ‖ξ s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a‖ * ‖ξ s‖ := mul_le_mul_of_nonneg_right (norm_rep_act_le ρ a s) (norm_nonneg _)
      _ = ‖((‖a‖ : ℂ) • (⇑ξ : G → H)) s‖ := by
        rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg a)]⟩
  map_add' ξ η := by
    apply lp.ext
    funext s
    change ρ (GCStarAlgebra.act (A := A) s⁻¹ a) ((⇑(ξ + η)) s) =
      ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s) + ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (η s)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c ξ := by
    apply lp.ext
    funext s
    change ρ (GCStarAlgebra.act (A := A) s⁻¹ a) ((⇑(c • ξ)) s) =
      c • ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]

theorem diagLinear_apply (a : A) (ξ : L2 G H) (s : G) :
    diagLinear ρ a ξ s = ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s) :=
  rfl

/-- The twisted diagonal action of one element, as a bounded operator. -/
def diagOp (a : A) : L2 G H →L[ℂ] L2 G H :=
  LinearMap.mkContinuous (diagLinear ρ a) ‖a‖ fun ξ => by
    calc ‖diagLinear ρ a ξ‖ ≤ ‖(‖a‖ : ℂ) • ξ‖ := by
          refine lp.norm_mono (by norm_num) fun s => ?_
          rw [diagLinear_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
          calc ‖ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s)‖
              ≤ ‖ρ (GCStarAlgebra.act (A := A) s⁻¹ a)‖ * ‖ξ s‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖a‖ * ‖ξ s‖ :=
                mul_le_mul_of_nonneg_right (norm_rep_act_le ρ a s) (norm_nonneg _)
      _ = ‖a‖ * ‖ξ‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]

theorem diagOp_apply (a : A) (ξ : L2 G H) (s : G) :
    diagOp ρ a ξ s = ρ (GCStarAlgebra.act (A := A) s⁻¹ a) (ξ s) :=
  rfl

end

end GroupApproximation.Full.TWWUCT.CrossedProduct
