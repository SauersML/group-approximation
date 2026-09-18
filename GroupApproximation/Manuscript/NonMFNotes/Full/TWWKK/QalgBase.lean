import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgUniversal

/-!
# Cuntz's algebra `qA`: definition, functoriality and the flip

`qA` is the kernel of the fold map `A * A → Ã` (`ι, ῑ ↦ A ⊆ Ã`) on the full unital free product.
It is a closed two-sided `⋆`-ideal of `A * A`, hence a non-unital C⋆-algebra in the universe of
`A`.  A `⋆`-homomorphism `f : A → B` induces `f * f : A * A → B * B` which preserves the kernels
of the fold maps, giving `Qalg.map f : qA → qB`; the flip `ι ↔ ῑ` restricts to
`Qalg.flip : qA → qA`, sending `q a = ι a - ῑ a` to `-q a`.

Source: J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(Tikuisis--White--Winter), lane TWWKK-Qalg, work order WO-TWWKK-A2.
-/

namespace GroupApproximation.Full.TWWKK

open FreeProd

universe u

noncomputable section

namespace FreeProd

variable {A B C : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- The flip of `A * A`, exchanging the two copies of `A`. -/
def swap (A : Type u) [NonUnitalCStarAlgebra A] : FreeUnital A →⋆ₐ[ℂ] FreeUnital A :=
  lift (FreeUnital A) (ι₂ A) (ι₁ A)

theorem swap_ι₁ (a : A) : swap A (ι₁ A a) = ι₂ A a :=
  lift_ι₁ (FreeUnital A) (ι₂ A) (ι₁ A) a

theorem swap_ι₂ (a : A) : swap A (ι₂ A a) = ι₁ A a :=
  lift_ι₂ (FreeUnital A) (ι₂ A) (ι₁ A) a

theorem swap_swap (A : Type u) [NonUnitalCStarAlgebra A] :
    (swap A).comp (swap A) = StarAlgHom.id ℂ (FreeUnital A) :=
  hom_ext (fun a => (congrArg (swap A) (swap_ι₁ a)).trans (swap_ι₂ a))
    (fun a => (congrArg (swap A) (swap_ι₂ a)).trans (swap_ι₁ a))

/-- The fold map `A * A → Ã`, identifying both copies of `A` with `A ⊆ Ã`. -/
def fold (A : Type u) [NonUnitalCStarAlgebra A] : FreeUnital A →⋆ₐ[ℂ] Unitization ℂ A :=
  lift (Unitization ℂ A) (Unitization.inrNonUnitalStarAlgHom ℂ A)
    (Unitization.inrNonUnitalStarAlgHom ℂ A)

theorem fold_ι₁ (a : A) : fold A (ι₁ A a) = (a : Unitization ℂ A) :=
  lift_ι₁ (Unitization ℂ A) (Unitization.inrNonUnitalStarAlgHom ℂ A)
    (Unitization.inrNonUnitalStarAlgHom ℂ A) a

theorem fold_ι₂ (a : A) : fold A (ι₂ A a) = (a : Unitization ℂ A) :=
  lift_ι₂ (Unitization ℂ A) (Unitization.inrNonUnitalStarAlgHom ℂ A)
    (Unitization.inrNonUnitalStarAlgHom ℂ A) a

theorem fold_comp_swap (A : Type u) [NonUnitalCStarAlgebra A] :
    (fold A).comp (swap A) = fold A :=
  hom_ext (fun a => (congrArg (fold A) (swap_ι₁ a)).trans ((fold_ι₂ a).trans (fold_ι₁ a).symm))
    (fun a => (congrArg (fold A) (swap_ι₂ a)).trans ((fold_ι₁ a).trans (fold_ι₂ a).symm))

/-- The free product `f * f : A * A → B * B` of a `⋆`-homomorphism with itself. -/
def freeMap (f : A →⋆ₙₐ[ℂ] B) : FreeUnital A →⋆ₐ[ℂ] FreeUnital B :=
  lift (FreeUnital B) ((ι₁ B).comp f) ((ι₂ B).comp f)

theorem freeMap_ι₁ (f : A →⋆ₙₐ[ℂ] B) (a : A) : freeMap f (ι₁ A a) = ι₁ B (f a) :=
  lift_ι₁ (FreeUnital B) ((ι₁ B).comp f) ((ι₂ B).comp f) a

theorem freeMap_ι₂ (f : A →⋆ₙₐ[ℂ] B) (a : A) : freeMap f (ι₂ A a) = ι₂ B (f a) :=
  lift_ι₂ (FreeUnital B) ((ι₁ B).comp f) ((ι₂ B).comp f) a

theorem freeMap_id (A : Type u) [NonUnitalCStarAlgebra A] :
    freeMap (NonUnitalStarAlgHom.id ℂ A) = StarAlgHom.id ℂ (FreeUnital A) :=
  hom_ext (fun a => freeMap_ι₁ (NonUnitalStarAlgHom.id ℂ A) a)
    (fun a => freeMap_ι₂ (NonUnitalStarAlgHom.id ℂ A) a)

theorem freeMap_comp (g : B →⋆ₙₐ[ℂ] C) (f : A →⋆ₙₐ[ℂ] B) :
    freeMap (g.comp f) = (freeMap g).comp (freeMap f) :=
  hom_ext
    (fun a => (freeMap_ι₁ (g.comp f) a).trans
      ((congrArg (freeMap g) (freeMap_ι₁ f a)).trans (freeMap_ι₁ g (f a))).symm)
    (fun a => (freeMap_ι₂ (g.comp f) a).trans
      ((congrArg (freeMap g) (freeMap_ι₂ f a)).trans (freeMap_ι₂ g (f a))).symm)

theorem fold_comp_freeMap (f : A →⋆ₙₐ[ℂ] B) :
    (fold B).comp (freeMap f) = (Unitization.starMap f).comp (fold A) :=
  hom_ext
    (fun a => (congrArg (fold B) (freeMap_ι₁ f a)).trans ((fold_ι₁ (f a)).trans
      ((Unitization.starMap_inr f a).symm.trans
        (congrArg (Unitization.starMap f) (fold_ι₁ a).symm))))
    (fun a => (congrArg (fold B) (freeMap_ι₂ f a)).trans ((fold_ι₂ (f a)).trans
      ((Unitization.starMap_inr f a).symm.trans
        (congrArg (Unitization.starMap f) (fold_ι₂ a).symm))))

end FreeProd

namespace Qalg

variable {A B C : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- The ideal `qA = ker (A * A → Ã)` of the full free product. -/
def ideal (A : Type u) [NonUnitalCStarAlgebra A] :
    NonUnitalStarSubalgebra ℂ (FreeUnital A) :=
  NonUnitalStarSubalgebra.comap (fold A) (⊥ : NonUnitalStarSubalgebra ℂ (Unitization ℂ A))

theorem mem_ideal {x : FreeUnital A} : x ∈ ideal A ↔ fold A x = 0 :=
  (NonUnitalStarSubalgebra.mem_comap ⊥ (fold A) x).trans NonUnitalStarAlgebra.mem_bot

theorem coe_ideal (A : Type u) [NonUnitalCStarAlgebra A] :
    (ideal A : Set (FreeUnital A)) = {x | fold A x = 0} := by
  ext x
  rw [SetLike.mem_coe, Set.mem_setOf_eq]
  exact mem_ideal

instance isClosed_ideal (A : Type u) [NonUnitalCStarAlgebra A] :
    IsClosed (ideal A : Set (FreeUnital A)) := by
  rw [coe_ideal]
  exact isClosed_eq (continuous_ofStarAlgHom (fold A)) continuous_const

theorem mul_mem_left {x : FreeUnital A} (hx : x ∈ ideal A) (y : FreeUnital A) :
    y * x ∈ ideal A := by
  rw [mem_ideal, map_mul, mem_ideal.mp hx, mul_zero]

theorem mul_mem_right {x : FreeUnital A} (hx : x ∈ ideal A) (y : FreeUnital A) :
    x * y ∈ ideal A := by
  rw [mem_ideal, map_mul, mem_ideal.mp hx, zero_mul]

end Qalg

/-- **Cuntz's algebra** `qA`, the kernel of the fold map on the full free product `A * A`. -/
abbrev Qalg (A : Type u) [NonUnitalCStarAlgebra A] : Type u :=
  ↥(Qalg.ideal A)

namespace Qalg

variable {A B C : Type u} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- `qA` is a non-unital C⋆-algebra (a closed `⋆`-subalgebra of `A * A`). -/
instance instNonUnitalCStarAlgebra : NonUnitalCStarAlgebra (Qalg A) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (Qalg.ideal A)

/-- The generator `q a = ι a - ῑ a` of `qA`. -/
def q (A : Type u) [NonUnitalCStarAlgebra A] (a : A) : Qalg A :=
  ⟨ι₁ A a - ι₂ A a, mem_ideal.mpr (by rw [map_sub, fold_ι₁, fold_ι₂, sub_self])⟩

theorem coe_q (a : A) : (q A a : FreeUnital A) = ι₁ A a - ι₂ A a :=
  rfl

/-- Restriction of a unital `⋆`-homomorphism on `A * A` to `qA`, with values in a
`⋆`-subalgebra containing the image of `qA`. -/
def restrict {E : Type*} [CStarAlgebra E] (F : FreeUnital A →⋆ₐ[ℂ] E)
    (S : NonUnitalStarSubalgebra ℂ E) (h : ∀ x, x ∈ ideal A → F x ∈ S) : Qalg A →⋆ₙₐ[ℂ] S :=
  NonUnitalStarAlgHom.codRestrict
    (F.toNonUnitalStarAlgHom.comp (NonUnitalStarSubalgebraClass.subtype (ideal A))) S
    (fun x => h x x.2)

theorem coe_restrict {E : Type*} [CStarAlgebra E] (F : FreeUnital A →⋆ₐ[ℂ] E)
    (S : NonUnitalStarSubalgebra ℂ E) (h : ∀ x, x ∈ ideal A → F x ∈ S) (x : Qalg A) :
    (restrict F S h x : E) = F x :=
  rfl

theorem freeMap_mem (f : A →⋆ₙₐ[ℂ] B) (x : FreeUnital A) (hx : x ∈ ideal A) :
    freeMap f x ∈ ideal B :=
  mem_ideal.mpr ((DFunLike.congr_fun (fold_comp_freeMap f) x).trans
    ((congrArg (Unitization.starMap f) (mem_ideal.mp hx)).trans (map_zero _)))

/-- **Functoriality**: `q f : qA → qB`, the restriction of `f * f`. -/
def map (f : A →⋆ₙₐ[ℂ] B) : Qalg A →⋆ₙₐ[ℂ] Qalg B :=
  restrict (freeMap f) (ideal B) (freeMap_mem f)

theorem coe_map (f : A →⋆ₙₐ[ℂ] B) (x : Qalg A) :
    (map f x : FreeUnital B) = freeMap f x :=
  rfl

theorem map_q (f : A →⋆ₙₐ[ℂ] B) (a : A) : map f (q A a) = q B (f a) :=
  Subtype.ext ((map_sub (freeMap f) (ι₁ A a) (ι₂ A a)).trans
    (congrArg₂ (· - ·) (freeMap_ι₁ f a) (freeMap_ι₂ f a)))

theorem map_id (A : Type u) [NonUnitalCStarAlgebra A] :
    map (NonUnitalStarAlgHom.id ℂ A) = NonUnitalStarAlgHom.id ℂ (Qalg A) :=
  NonUnitalStarAlgHom.ext fun x =>
    Subtype.ext (DFunLike.congr_fun (freeMap_id A) (x : FreeUnital A))

theorem map_comp (g : B →⋆ₙₐ[ℂ] C) (f : A →⋆ₙₐ[ℂ] B) :
    map (g.comp f) = (map g).comp (map f) :=
  NonUnitalStarAlgHom.ext fun x =>
    Subtype.ext (DFunLike.congr_fun (freeMap_comp g f) (x : FreeUnital A))

theorem swap_mem (x : FreeUnital A) (hx : x ∈ ideal A) : swap A x ∈ ideal A :=
  mem_ideal.mpr ((DFunLike.congr_fun (fold_comp_swap A) x).trans (mem_ideal.mp hx))

/-- The **flip** of `qA`, induced by exchanging the two copies of `A`. -/
def flip (A : Type u) [NonUnitalCStarAlgebra A] : Qalg A →⋆ₙₐ[ℂ] Qalg A :=
  restrict (swap A) (ideal A) swap_mem

theorem coe_flip (x : Qalg A) : (flip A x : FreeUnital A) = swap A x :=
  rfl

theorem flip_q (a : A) : flip A (q A a) = -q A a :=
  Subtype.ext ((map_sub (swap A) (ι₁ A a) (ι₂ A a)).trans
    ((congrArg₂ (· - ·) (swap_ι₁ a) (swap_ι₂ a)).trans (neg_sub (ι₁ A a) (ι₂ A a)).symm))

theorem flip_flip (A : Type u) [NonUnitalCStarAlgebra A] :
    (flip A).comp (flip A) = NonUnitalStarAlgHom.id ℂ (Qalg A) :=
  NonUnitalStarAlgHom.ext fun x =>
    Subtype.ext (DFunLike.congr_fun (swap_swap A) (x : FreeUnital A))

theorem map_flip (f : A →⋆ₙₐ[ℂ] B) : (map f).comp (flip A) = (flip B).comp (map f) := by
  have h : (freeMap f).comp (swap A) = (swap B).comp (freeMap f) :=
    hom_ext
      (fun a => (congrArg (freeMap f) (swap_ι₁ a)).trans ((freeMap_ι₂ f a).trans
        ((swap_ι₁ (f a)).symm.trans (congrArg (swap B) (freeMap_ι₁ f a).symm))))
      (fun a => (congrArg (freeMap f) (swap_ι₂ a)).trans ((freeMap_ι₁ f a).trans
        ((swap_ι₂ (f a)).symm.trans (congrArg (swap B) (freeMap_ι₂ f a).symm))))
  exact NonUnitalStarAlgHom.ext fun x =>
    Subtype.ext (DFunLike.congr_fun h (x : FreeUnital A))

end Qalg

end

end GroupApproximation.Full.TWWKK
