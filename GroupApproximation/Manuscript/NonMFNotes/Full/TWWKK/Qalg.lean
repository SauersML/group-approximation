import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgBase

/-!
# Cuntz's algebra `qA`: homotopy invariance, the projection `π` and the universal lift

This file completes the basic API of `qA = ker (A * A → Ã)` (defined in `QalgBase`):

* `Qalg.map_nhomotopic`: `q` sends homotopic `⋆`-homomorphisms to homotopic ones;
* `Qalg.pi : qA → A`, the restriction of the map `A * A → Ã` with `ι ↦ id`, `ῑ ↦ 0`,
  satisfying `π (q a) = a`;
* `Qalg.lift`: a pair `φ, ψ : A → D` with `φ a - ψ a` in a closed two-sided `⋆`-ideal `J`
  (a quasihomomorphism, Cuntz's `(φ, ψ) : A ⇉ D ▷ J`) induces `qA → J`,
  `q a ↦ φ a - ψ a`.

Source: J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(Tikuisis--White--Winter), lane TWWKK-Qalg, work order WO-TWWKK-A2.
-/

namespace GroupApproximation.Full.TWWKK

open FreeProd

universe u

noncomputable section

namespace FreeProd

variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- Unital `⋆`-homomorphisms between C⋆-algebras are `1`-Lipschitz. -/
theorem dist_apply_le {E F : Type*} [CStarAlgebra E] [CStarAlgebra F] (f : E →⋆ₐ[ℂ] F)
    (x y : E) : dist (f x) (f y) ≤ dist x y := by
  rw [dist_eq_norm_sub, dist_eq_norm_sub, ← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le f (x - y)

/-- For a pointwise continuous path `k` of `⋆`-homomorphisms, `t ↦ (k t * k t) y` is
continuous for every `y ∈ A * A`. -/
theorem continuous_freeMap_path (k : ℝ → (A →⋆ₙₐ[ℂ] B))
    (hk : ∀ a, Continuous fun t : ℝ => k t a) (y : FreeUnital A) :
    Continuous fun t : ℝ => freeMap (k t) y := by
  refine FreeProd.induction (p := fun y => Continuous fun t : ℝ => freeMap (k t) y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y
  · refine isClosed_of_closure_subset fun y hy => ?_
    show Continuous fun t : ℝ => freeMap (k t) y
    refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
    obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.mp hu
    obtain ⟨z, hz, hyz⟩ := Metric.mem_closure_iff.mp hy ε hε
    exact ⟨fun t => freeMap (k t) z, hz,
      fun t => hu ((dist_apply_le (freeMap (k t)) y z).trans_lt hyz)⟩
  · exact continuous_const.congr fun t => (map_one (freeMap (k t))).symm
  · intro a
    exact ((continuous_nonUnitalStarAlgHom (ι₁ B)).comp (hk a)).congr
      fun t => (freeMap_ι₁ (k t) a).symm
  · intro a
    exact ((continuous_nonUnitalStarAlgHom (ι₂ B)).comp (hk a)).congr
      fun t => (freeMap_ι₂ (k t) a).symm
  · intro x z hx hz
    exact (Continuous.add hx hz).congr fun t => (map_add (freeMap (k t)) x z).symm
  · intro x z hx hz
    exact (Continuous.mul hx hz).congr fun t => (map_mul (freeMap (k t)) x z).symm
  · intro c x hx
    exact (Continuous.const_smul hx c).congr fun t => (map_smul (freeMap (k t)) c x).symm
  · intro x hx
    exact (Continuous.star hx).congr fun t => (map_star (freeMap (k t)) x).symm

end FreeProd

namespace Qalg

variable {A B : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Homotopy invariance** of `q`: homotopic `⋆`-homomorphisms `f ≃ g` give homotopic
`q f ≃ q g`. -/
theorem map_nhomotopic {f g : A →⋆ₙₐ[ℂ] B} (h : NHomotopic f g) :
    NHomotopic (map f) (map g) := by
  obtain ⟨k, hk, h0, h1⟩ := h
  refine ⟨fun t => map (k t), fun x => ?_, ?_, ?_⟩
  · exact ((continuous_freeMap_path k hk (x : FreeUnital A)).subtype_mk
      (fun t => freeMap_mem (k t) x x.2)).congr fun t => Subtype.ext (coe_map (k t) x).symm
  · show map (k 0) = map f
    rw [h0]
  · show map (k 1) = map g
    rw [h1]

/-! ### The projection `π : qA → A` -/

/-- The unital `⋆`-homomorphism `A * A → Ã` with `ι ↦ id` and `ῑ ↦ 0`. -/
def piPre (A : Type u) [NonUnitalCStarAlgebra A] : FreeUnital A →⋆ₐ[ℂ] Unitization ℂ A :=
  FreeProd.lift (Unitization ℂ A) (Unitization.inrNonUnitalStarAlgHom ℂ A) 0

theorem piPre_ι₁ (a : A) : piPre A (ι₁ A a) = (a : Unitization ℂ A) :=
  lift_ι₁ (Unitization ℂ A) (Unitization.inrNonUnitalStarAlgHom ℂ A) 0 a

theorem piPre_ι₂ (a : A) : piPre A (ι₂ A a) = 0 :=
  (lift_ι₂ (Unitization ℂ A) (Unitization.inrNonUnitalStarAlgHom ℂ A) 0 a).trans
    (NonUnitalStarAlgHom.zero_apply a)

/-- `Unitization.starMap φ` preserves the scalar part. -/
theorem fst_starMap (φ : A →⋆ₙₐ[ℂ] A) (x : Unitization ℂ A) :
    (Unitization.starMap φ x).fst = x.fst := by
  conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq x]
  rw [map_add, Unitization.starMap_inl, Unitization.starMap_inr, Unitization.fst_add,
    Unitization.algebraMap_eq_inl, Unitization.fst_inl, Unitization.fst_inr, add_zero]

theorem starMap_zero_fold_ι₂ (a : A) :
    Unitization.starMap (0 : A →⋆ₙₐ[ℂ] A) (fold A (ι₂ A a)) = 0 :=
  (congrArg (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] A)) (fold_ι₂ a)).trans
    ((Unitization.starMap_inr (0 : A →⋆ₙₐ[ℂ] A) a).trans
      ((congrArg (fun b : A => (b : Unitization ℂ A))
        (NonUnitalStarAlgHom.zero_apply (R := ℂ) (B := A) a)).trans (Unitization.inr_zero ℂ)))

theorem starMap_zero_comp_piPre (A : Type u) [NonUnitalCStarAlgebra A] :
    (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] A)).comp (piPre A) =
      (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] A)).comp (fold A) :=
  hom_ext
    (fun a => congrArg (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] A))
      ((piPre_ι₁ a).trans (fold_ι₁ a).symm))
    (fun a => (congrArg (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] A)) (piPre_ι₂ a)).trans
      ((map_zero (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] A))).trans (starMap_zero_fold_ι₂ a).symm))

/-- `piPre` and the fold map have the same scalar part. -/
theorem fst_piPre (x : FreeUnital A) : (piPre A x).fst = (fold A x).fst :=
  (fst_starMap 0 (piPre A x)).symm.trans
    ((congrArg Unitization.fst (DFunLike.congr_fun (starMap_zero_comp_piPre A) x)).trans
      (fst_starMap 0 (fold A x)))

theorem fst_piPre_of_mem {x : FreeUnital A} (hx : x ∈ ideal A) : (piPre A x).fst = 0 :=
  (fst_piPre x).trans ((congrArg Unitization.fst (mem_ideal.mp hx)).trans Unitization.fst_zero)

/-- **The projection** `π : qA → A`, `π (q a) = a`. -/
def pi (A : Type u) [NonUnitalCStarAlgebra A] : Qalg A →⋆ₙₐ[ℂ] A where
  toFun x := (piPre A x).snd
  map_zero' := (congrArg Unitization.snd (map_zero (piPre A))).trans Unitization.snd_zero
  map_add' x y := (congrArg Unitization.snd
    (map_add (piPre A) (x : FreeUnital A) (y : FreeUnital A))).trans (Unitization.snd_add _ _)
  map_smul' c x := (congrArg Unitization.snd
    (map_smul (piPre A) c (x : FreeUnital A))).trans (Unitization.snd_smul c _)
  map_mul' x y := by
    show (piPre A ((x : FreeUnital A) * (y : FreeUnital A))).snd =
      (piPre A x).snd * (piPre A y).snd
    rw [map_mul, Unitization.snd_mul, fst_piPre_of_mem x.2, fst_piPre_of_mem y.2,
      zero_smul ℂ, zero_smul ℂ, zero_add, zero_add]
  map_star' x := (congrArg Unitization.snd
    (map_star (piPre A) (x : FreeUnital A))).trans (Unitization.snd_star _)

theorem pi_apply (x : Qalg A) : pi A x = (piPre A x).snd :=
  rfl

theorem pi_q (a : A) : pi A (q A a) = a := by
  show (piPre A (ι₁ A a - ι₂ A a)).snd = a
  rw [map_sub, piPre_ι₁, piPre_ι₂, sub_zero, Unitization.snd_inr]

/-! ### The universal lift of a quasihomomorphism -/

/-- `Unitization.starLift φ` extends `φ`. -/
theorem starLift_inr {D : Type u} [CStarAlgebra D] (φ : A →⋆ₙₐ[ℂ] D) (a : A) :
    Unitization.starLift φ (a : Unitization ℂ A) = φ a :=
  (Unitization.starLift_symm_apply_apply (Unitization.starLift φ) a).symm.trans
    (congrArg (fun χ : A →⋆ₙₐ[ℂ] D => χ a) (Equiv.symm_apply_apply Unitization.starLift φ))

/-- The diagonal lift `φ * φ` factors through the fold map. -/
theorem lift_self_eq {D : Type u} [CStarAlgebra D] (φ : A →⋆ₙₐ[ℂ] D) :
    FreeProd.lift D φ φ = (Unitization.starLift φ).comp (fold A) :=
  hom_ext
    (fun a => (lift_ι₁ D φ φ a).trans
      ((starLift_inr φ a).symm.trans (congrArg (Unitization.starLift φ) (fold_ι₁ a).symm)))
    (fun a => (lift_ι₂ D φ φ a).trans
      ((starLift_inr φ a).symm.trans (congrArg (Unitization.starLift φ) (fold_ι₂ a).symm)))

theorem lift_self_of_mem {D : Type u} [CStarAlgebra D] (φ : A →⋆ₙₐ[ℂ] D) {x : FreeUnital A}
    (hx : x ∈ ideal A) : FreeProd.lift D φ φ x = 0 :=
  (DFunLike.congr_fun (lift_self_eq φ) x).trans
    ((congrArg (Unitization.starLift φ) (mem_ideal.mp hx)).trans (map_zero _))

/-- For a quasihomomorphism `(φ, ψ)` into a closed two-sided `⋆`-ideal `J`, the difference
`(φ * ψ) y - (φ * φ) y` lies in `J` for every `y ∈ A * A`. -/
theorem lift_sub_lift_mem {D : Type u} [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D)
    (J : NonUnitalStarSubalgebra ℂ D) (hJ : IsClosed (J : Set D))
    (hJi : ∀ d x : D, x ∈ J → d * x ∈ J ∧ x * d ∈ J) (hφψ : ∀ a, φ a - ψ a ∈ J)
    (y : FreeUnital A) : FreeProd.lift D φ ψ y - FreeProd.lift D φ φ y ∈ J := by
  refine FreeProd.induction
    (p := fun y => FreeProd.lift D φ ψ y - FreeProd.lift D φ φ y ∈ J) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y
  · exact IsClosed.preimage
      ((continuous_ofStarAlgHom (FreeProd.lift D φ ψ)).sub
        (continuous_ofStarAlgHom (FreeProd.lift D φ φ))) hJ
  · show FreeProd.lift D φ ψ 1 - FreeProd.lift D φ φ 1 ∈ J
    rw [map_one, map_one, sub_self]
    exact zero_mem J
  · intro a
    show FreeProd.lift D φ ψ (ι₁ A a) - FreeProd.lift D φ φ (ι₁ A a) ∈ J
    rw [lift_ι₁, lift_ι₁, sub_self]
    exact zero_mem J
  · intro a
    show FreeProd.lift D φ ψ (ι₂ A a) - FreeProd.lift D φ φ (ι₂ A a) ∈ J
    rw [lift_ι₂, lift_ι₂, ← neg_sub]
    exact neg_mem (hφψ a)
  · intro x z hx hz
    show FreeProd.lift D φ ψ (x + z) - FreeProd.lift D φ φ (x + z) ∈ J
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hx hz
  · intro x z hx hz
    show FreeProd.lift D φ ψ (x * z) - FreeProd.lift D φ φ (x * z) ∈ J
    rw [map_mul, map_mul]
    have h : FreeProd.lift D φ ψ x * FreeProd.lift D φ ψ z -
        FreeProd.lift D φ φ x * FreeProd.lift D φ φ z =
        (FreeProd.lift D φ ψ x - FreeProd.lift D φ φ x) * FreeProd.lift D φ ψ z +
          FreeProd.lift D φ φ x * (FreeProd.lift D φ ψ z - FreeProd.lift D φ φ z) := by
      rw [sub_mul, mul_sub, sub_add_sub_cancel]
    rw [h]
    exact add_mem (hJi (FreeProd.lift D φ ψ z) _ hx).2 (hJi (FreeProd.lift D φ φ x) _ hz).1
  · intro c x hx
    show FreeProd.lift D φ ψ (c • x) - FreeProd.lift D φ φ (c • x) ∈ J
    rw [map_smul, map_smul, ← smul_sub]
    exact SMulMemClass.smul_mem c hx
  · intro x hx
    show FreeProd.lift D φ ψ (star x) - FreeProd.lift D φ φ (star x) ∈ J
    rw [map_star, map_star, ← star_sub]
    exact star_mem hx

theorem lift_mem {D : Type u} [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D)
    (J : NonUnitalStarSubalgebra ℂ D) (hJ : IsClosed (J : Set D))
    (hJi : ∀ d x : D, x ∈ J → d * x ∈ J ∧ x * d ∈ J) (hφψ : ∀ a, φ a - ψ a ∈ J)
    (x : FreeUnital A) (hx : x ∈ ideal A) : FreeProd.lift D φ ψ x ∈ J := by
  have h := lift_sub_lift_mem φ ψ J hJ hJi hφψ x
  rw [lift_self_of_mem φ hx, sub_zero] at h
  exact h

/-- **Universal property of `qA`**: a quasihomomorphism `(φ, ψ) : A ⇉ D ▷ J`, i.e. a pair of
`⋆`-homomorphisms with `φ a - ψ a` in a closed two-sided `⋆`-ideal `J` of `D`, induces the
`⋆`-homomorphism `qA → J`, `q a ↦ φ a - ψ a` (the restriction of `φ * ψ`). -/
def lift {D : Type u} [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D)
    (J : NonUnitalStarSubalgebra ℂ D) (hJ : IsClosed (J : Set D))
    (hJi : ∀ d x : D, x ∈ J → d * x ∈ J ∧ x * d ∈ J) (hφψ : ∀ a, φ a - ψ a ∈ J) :
    Qalg A →⋆ₙₐ[ℂ] J :=
  restrict (FreeProd.lift D φ ψ) J (lift_mem φ ψ J hJ hJi hφψ)

theorem coe_lift {D : Type u} [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D)
    (J : NonUnitalStarSubalgebra ℂ D) (hJ : IsClosed (J : Set D))
    (hJi : ∀ d x : D, x ∈ J → d * x ∈ J ∧ x * d ∈ J) (hφψ : ∀ a, φ a - ψ a ∈ J)
    (x : Qalg A) : (lift φ ψ J hJ hJi hφψ x : D) = FreeProd.lift D φ ψ x :=
  rfl

theorem lift_q {D : Type u} [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D)
    (J : NonUnitalStarSubalgebra ℂ D) (hJ : IsClosed (J : Set D))
    (hJi : ∀ d x : D, x ∈ J → d * x ∈ J ∧ x * d ∈ J) (hφψ : ∀ a, φ a - ψ a ∈ J) (a : A) :
    (lift φ ψ J hJ hJi hφψ (q A a) : D) = φ a - ψ a :=
  (map_sub (FreeProd.lift D φ ψ) (ι₁ A a) (ι₂ A a)).trans
    (congrArg₂ (· - ·) (lift_ι₁ D φ ψ a) (lift_ι₂ D φ ψ a))

/-- The lift of the pair `(ι, ῑ)` itself, into `J = qA ⊆ A * A`, is the identity of `qA`. -/
theorem lift_ι_eq_id :
    lift (ι₁ A) (ι₂ A) (ideal A) (isClosed_ideal A)
      (fun d x hx => ⟨mul_mem_left hx d, mul_mem_right hx d⟩)
      (fun a => (q A a).2) = NonUnitalStarAlgHom.id ℂ (Qalg A) :=
  NonUnitalStarAlgHom.ext fun x => Subtype.ext
    (DFunLike.congr_fun (hom_ext (f := FreeProd.lift (FreeUnital A) (ι₁ A) (ι₂ A))
      (g := StarAlgHom.id ℂ (FreeUnital A)) (lift_ι₁ (FreeUnital A) (ι₁ A) (ι₂ A))
      (lift_ι₂ (FreeUnital A) (ι₁ A) (ι₂ A))) (x : FreeUnital A))

end Qalg

end

end GroupApproximation.Full.TWWKK
