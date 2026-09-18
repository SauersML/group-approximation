import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgPre

/-!
# The universal C⋆-norm on the algebraic free product

For `x : PreFree A` (`QalgPre`) we set `‖x‖ := sup_{(D, φ, ψ)} ‖x(φ, ψ)‖`, the supremum over all
pairs of `⋆`-homomorphisms `φ, ψ : A → D` into unital C⋆-algebras in the universe of `A`.  It is
realized through the injective `⋆`-homomorphism `toLp` into `ℓ^∞` over all pairs, so `PreFree A`
is a normed `⋆`-algebra satisfying the C⋆-identity.  Evaluation at a pair is a contractive unital
`⋆`-homomorphism `evalHom`, and the two copies of `A` are `gen₁Hom`, `gen₂Hom`.

This is the universal norm of the full unital C⋆-free product `A * A` in Cuntz's construction of
`qA` (J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(Tikuisis--White--Winter), lane TWWKK-Qalg, work order WO-TWWKK-A2.
-/

namespace GroupApproximation.Full.TWWKK

namespace FreeProd

open scoped ENNReal

universe u

noncomputable section

variable {A : Type u} [NonUnitalCStarAlgebra A]

theorem memℓp_toPi (x : PreFree A) : Memℓp (toPi x) ∞ := by
  obtain ⟨s, rfl⟩ := exists_mk x
  refine memℓp_infty ⟨termBound s, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact norm_evalTerm_le i s

/-- The embedding of `PreFree A` into `ℓ^∞` over all representations. -/
def toLp : PreFree A →ₙ+* lp (fun i : Rep A => i.D) ∞ where
  toFun x := ⟨toPi x, memℓp_toPi x⟩
  map_mul' x y := lp.ext (toPi_mul x y)
  map_zero' := lp.ext toPi_zero
  map_add' x y := lp.ext (toPi_add x y)

theorem toLp_apply (x : PreFree A) (i : Rep A) : toLp x i = evalQ i x :=
  rfl

theorem toLp_injective : Function.Injective (toLp (A := A)) := fun x y h =>
  toPi_injective (congrArg (fun f : lp (fun i : Rep A => i.D) ∞ => (f : ∀ i : Rep A, i.D)) h)

theorem toLp_smul (c : ℂ) (x : PreFree A) : toLp (c • x) = c • toLp x :=
  lp.ext (toPi_smul c x)

theorem toLp_star (x : PreFree A) : toLp (star x) = star (toLp x) :=
  lp.ext (toPi_star x)

instance instNormedRing : NormedRing (PreFree A) :=
  { NonUnitalNormedRing.induced (PreFree A) (lp (fun i : Rep A => i.D) ∞) toLp toLp_injective,
    instRing (A := A) with }

theorem norm_def (x : PreFree A) : ‖x‖ = ‖toLp x‖ :=
  rfl

instance instNormedSpace : NormedSpace ℂ (PreFree A) where
  norm_smul_le c x := by
    rw [norm_def, norm_def, toLp_smul]
    exact norm_smul_le c (toLp x)

instance instNormedAlgebra : NormedAlgebra ℂ (PreFree A) where
  norm_smul_le := norm_smul_le

instance instCStarRing : CStarRing (PreFree A) where
  norm_mul_self_le x := by
    rw [norm_def, norm_def, map_mul, toLp_star]
    exact CStarRing.norm_mul_self_le (toLp x)

/-- Every value of `x` is bounded by the norm of `x`. -/
theorem norm_evalQ_le (i : Rep A) (x : PreFree A) : ‖evalQ i x‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero (toLp x) i

/-! ## Evaluation and generators -/

/-- **Evaluation at a representation**, a unital `⋆`-homomorphism. -/
def evalHom (i : Rep A) : PreFree A →⋆ₐ[ℂ] i.D where
  toFun := evalQ i
  map_one' := rfl
  map_mul' x y := congrFun (toPi_mul x y) i
  map_zero' := rfl
  map_add' x y := congrFun (toPi_add x y) i
  commutes' c :=
    (congrFun (toPi_smul c (1 : PreFree A)) i).trans (Algebra.algebraMap_eq_smul_one c).symm
  map_star' x := congrFun (toPi_star x) i

theorem evalHom_apply (i : Rep A) (x : PreFree A) : evalHom i x = evalQ i x :=
  rfl

/-- The first copy of `A` in the free product. -/
def gen₁Hom : A →⋆ₙₐ[ℂ] PreFree A where
  toFun a := mk (.gen₁ a)
  map_smul' c a := mk_eq_mk (s := .gen₁ (c • a)) (t := .smul c (.gen₁ a))
    fun i => map_smul i.φ c a
  map_zero' := mk_eq_mk (s := .gen₁ 0) (t := .zero) fun i => map_zero i.φ
  map_add' a b := mk_eq_mk (s := .gen₁ (a + b)) (t := .add (.gen₁ a) (.gen₁ b))
    fun i => map_add i.φ a b
  map_mul' a b := mk_eq_mk (s := .gen₁ (a * b)) (t := .mul (.gen₁ a) (.gen₁ b))
    fun i => map_mul i.φ a b
  map_star' a := mk_eq_mk (s := .gen₁ (star a)) (t := .adj (.gen₁ a))
    fun i => map_star i.φ a

/-- The second copy of `A` in the free product. -/
def gen₂Hom : A →⋆ₙₐ[ℂ] PreFree A where
  toFun a := mk (.gen₂ a)
  map_smul' c a := mk_eq_mk (s := .gen₂ (c • a)) (t := .smul c (.gen₂ a))
    fun i => map_smul i.ψ c a
  map_zero' := mk_eq_mk (s := .gen₂ 0) (t := .zero) fun i => map_zero i.ψ
  map_add' a b := mk_eq_mk (s := .gen₂ (a + b)) (t := .add (.gen₂ a) (.gen₂ b))
    fun i => map_add i.ψ a b
  map_mul' a b := mk_eq_mk (s := .gen₂ (a * b)) (t := .mul (.gen₂ a) (.gen₂ b))
    fun i => map_mul i.ψ a b
  map_star' a := mk_eq_mk (s := .gen₂ (star a)) (t := .adj (.gen₂ a))
    fun i => map_star i.ψ a

theorem evalHom_gen₁ (i : Rep A) (a : A) : evalHom i (gen₁Hom a) = i.φ a :=
  rfl

theorem evalHom_gen₂ (i : Rep A) (a : A) : evalHom i (gen₂Hom a) = i.ψ a :=
  rfl

/-- Two elements agreeing under every representation are equal. -/
theorem ext_evalHom {x y : PreFree A} (h : ∀ i : Rep A, evalHom i x = evalHom i y) : x = y :=
  toPi_injective (funext h)

end

end FreeProd

end GroupApproximation.Full.TWWKK
