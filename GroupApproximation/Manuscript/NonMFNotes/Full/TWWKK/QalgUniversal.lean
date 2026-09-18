import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgCompletion

/-!
# The universal property of the full free product `A * A`

Every pair `φ, ψ : A → D` of `⋆`-homomorphisms into a unital C⋆-algebra `D` in the universe of
`A` extends uniquely to a unital `⋆`-homomorphism `lift D φ ψ : A * A → D` with
`lift D φ ψ ∘ ι₁ = φ` and `lift D φ ψ ∘ ι₂ = ψ`.  Existence is the continuous extension of the
contractive evaluation `evalHom` (`QalgNorm`) to the completion.  Uniqueness comes from the
closed-induction principle `induction`: a closed property holding on `1`, on both copies of `A`,
and stable under the `⋆`-algebra operations holds on all of `A * A`.

This is the universal property of the full free product used by Cuntz
(J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(Tikuisis--White--Winter), lane TWWKK-Qalg, work order WO-TWWKK-A2.
-/

namespace GroupApproximation.Full.TWWKK

namespace FreeProd

open UniformSpace

universe u

noncomputable section

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Unital `⋆`-homomorphisms between C⋆-algebras are continuous. -/
theorem continuous_ofStarAlgHom {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : E →⋆ₐ[ℂ] F) : Continuous fun x : E => f x :=
  AddMonoidHomClass.continuous_of_bound f 1 fun x => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le f x

theorem continuous_evalHom (i : Rep A) :
    Continuous ((evalHom i).toRingHom : PreFree A → i.D) :=
  AddMonoidHomClass.continuous_of_bound (evalHom i).toRingHom 1 fun x => by
    rw [one_mul]
    exact norm_evalQ_le i x

/-- The continuous extension of evaluation to the completion, as a ring homomorphism. -/
def evalRing (i : Rep A) : FreeUnital A →+* i.D :=
  Completion.extensionHom (evalHom i).toRingHom (continuous_evalHom i)

theorem evalRing_coe (i : Rep A) (a : PreFree A) :
    evalRing i (a : Completion (PreFree A)) = evalHom i a :=
  Completion.extensionHom_coe (evalHom i).toRingHom (continuous_evalHom i) a

theorem continuous_evalRing (i : Rep A) : Continuous (evalRing i) :=
  Completion.continuous_extension (f := ((evalHom i).toRingHom : PreFree A → i.D))

theorem evalRing_star (i : Rep A) (x : FreeUnital A) :
    evalRing i (star x) = star (evalRing i x) := by
  refine Completion.induction_on x
    (isClosed_eq ((continuous_evalRing i).comp continuous_star) (continuous_evalRing i).star) ?_
  intro a
  exact ((congrArg (evalRing i) (star_coe a)).trans (evalRing_coe i (star a))).trans
    ((map_star (evalHom i) a).trans (congrArg star (evalRing_coe i a).symm))

theorem evalRing_algebraMap (i : Rep A) (c : ℂ) :
    evalRing i (algebraMap ℂ (FreeUnital A) c) = algebraMap ℂ i.D c :=
  (congrArg (evalRing i) (Completion.algebraMap_def (PreFree A) ℂ c)).trans
    ((evalRing_coe i (algebraMap ℂ (PreFree A) c)).trans (AlgHomClass.commutes (evalHom i) c))

/-- Evaluation at a representation, extended to `A * A`. -/
def evalC (i : Rep A) : FreeUnital A →⋆ₐ[ℂ] i.D where
  toFun := evalRing i
  map_one' := map_one (evalRing i)
  map_mul' := map_mul (evalRing i)
  map_zero' := map_zero (evalRing i)
  map_add' := map_add (evalRing i)
  commutes' := evalRing_algebraMap i
  map_star' := evalRing_star i

/-- **Universal property**: the unital `⋆`-homomorphism `A * A → D` determined by `φ` and `ψ`. -/
def lift (D : Type u) [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D) : FreeUnital A →⋆ₐ[ℂ] D :=
  evalC ⟨D, φ, ψ⟩

/-- The dense embedding `PreFree A → A * A`. -/
def coeHom : PreFree A →⋆ₐ[ℂ] FreeUnital A where
  toFun x := (x : Completion (PreFree A))
  map_one' := Completion.coe_one (PreFree A)
  map_mul' := Completion.coe_mul
  map_zero' := Completion.coe_zero
  map_add' := Completion.coe_add
  commutes' c := (Completion.algebraMap_def (PreFree A) ℂ c).symm
  map_star' x := (star_coe x).symm

/-- The first copy `ι` of `A` in `A * A`. -/
def ι₁ (A : Type u) [NonUnitalCStarAlgebra A] : A →⋆ₙₐ[ℂ] FreeUnital A :=
  (coeHom (A := A)).toNonUnitalStarAlgHom.comp gen₁Hom

/-- The second copy `ῑ` of `A` in `A * A`. -/
def ι₂ (A : Type u) [NonUnitalCStarAlgebra A] : A →⋆ₙₐ[ℂ] FreeUnital A :=
  (coeHom (A := A)).toNonUnitalStarAlgHom.comp gen₂Hom

theorem lift_ι₁ (D : Type u) [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D) (a : A) :
    lift D φ ψ (ι₁ A a) = φ a :=
  (evalRing_coe (⟨D, φ, ψ⟩ : Rep A) (gen₁Hom a)).trans (evalHom_gen₁ (⟨D, φ, ψ⟩ : Rep A) a)

theorem lift_ι₂ (D : Type u) [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D) (a : A) :
    lift D φ ψ (ι₂ A a) = ψ a :=
  (evalRing_coe (⟨D, φ, ψ⟩ : Rep A) (gen₂Hom a)).trans (evalHom_gen₂ (⟨D, φ, ψ⟩ : Rep A) a)

/-- **Closed induction** on `A * A`: a closed property containing `1` and both copies of `A` and
stable under the `⋆`-algebra operations holds everywhere. -/
theorem induction {p : FreeUnital A → Prop} (hp : IsClosed {x | p x}) (h1 : p 1)
    (hι₁ : ∀ a, p (ι₁ A a)) (hι₂ : ∀ a, p (ι₂ A a))
    (hadd : ∀ x y, p x → p y → p (x + y)) (hmul : ∀ x y, p x → p y → p (x * y))
    (hsmul : ∀ (c : ℂ) x, p x → p (c • x)) (hstar : ∀ x, p x → p (star x))
    (x : FreeUnital A) : p x := by
  refine Completion.induction_on x hp ?_
  intro a
  obtain ⟨s, rfl⟩ := exists_mk a
  induction s with
  | gen₁ b => exact hι₁ b
  | gen₂ b => exact hι₂ b
  | zero =>
    have h := hsmul 0 1 h1
    rw [zero_smul] at h
    exact h
  | one => exact h1
  | add s t ihs iht =>
    have h := hadd _ _ ihs iht
    rw [← Completion.coe_add] at h
    exact h
  | neg s ihs =>
    have h := hsmul (-1) _ ihs
    rw [neg_one_smul ℂ, ← Completion.coe_neg] at h
    exact h
  | mul s t ihs iht =>
    have h := hmul _ _ ihs iht
    rw [← Completion.coe_mul] at h
    exact h
  | smul c s ihs =>
    have h := hsmul c _ ihs
    rw [← Completion.coe_smul] at h
    exact h
  | adj s ihs =>
    have h := hstar _ ihs
    rw [star_coe] at h
    exact h

/-- Unital `⋆`-homomorphisms out of `A * A` are determined by their values on both copies. -/
theorem hom_ext {B : Type*} [CStarAlgebra B] {f g : FreeUnital A →⋆ₐ[ℂ] B}
    (h₁ : ∀ a, f (ι₁ A a) = g (ι₁ A a)) (h₂ : ∀ a, f (ι₂ A a) = g (ι₂ A a)) : f = g :=
  StarAlgHom.ext fun x => induction (p := fun x => f x = g x)
    (isClosed_eq (continuous_ofStarAlgHom f) (continuous_ofStarAlgHom g))
    ((map_one f).trans (map_one g).symm) h₁ h₂
    (fun x y hx hy =>
      (map_add f x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add g x y).symm))
    (fun x y hx hy =>
      (map_mul f x y).trans ((congrArg₂ (· * ·) hx hy).trans (map_mul g x y).symm))
    (fun c x hx =>
      (map_smul f c x).trans ((congrArg (c • ·) hx).trans (map_smul g c x).symm))
    (fun x hx => (map_star f x).trans ((congrArg star hx).trans (map_star g x).symm)) x

theorem lift_comp_ι₁ (D : Type u) [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D) :
    (lift D φ ψ).toNonUnitalStarAlgHom.comp (ι₁ A) = φ :=
  NonUnitalStarAlgHom.ext (lift_ι₁ D φ ψ)

theorem lift_comp_ι₂ (D : Type u) [CStarAlgebra D] (φ ψ : A →⋆ₙₐ[ℂ] D) :
    (lift D φ ψ).toNonUnitalStarAlgHom.comp (ι₂ A) = ψ :=
  NonUnitalStarAlgHom.ext (lift_ι₂ D φ ψ)

end

end FreeProd

end GroupApproximation.Full.TWWKK
