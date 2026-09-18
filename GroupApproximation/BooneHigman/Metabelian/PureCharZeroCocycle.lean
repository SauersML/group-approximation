import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.TypeTags.Basic
import GroupApproximation.BooneHigman.GroupRing.Semidirect
import GroupApproximation.BooneHigman.Statement.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The Kaloujnine–Krasner cocycle of a metabelian group (lane bh-met-19)

Let `Γ` be a group, `Q = Γᵃᵇ`, `X = (Γ')ᵃᵇ` and `s : Q → Γ` a set-theoretic section of the
abelianization map. The function `c_g : Q → X`, `c_g(x) = [s x · g · s(x ḡ)⁻¹]`, satisfies the
cocycle identity `c_{gh} = c_g + ḡ • c_h` for the translation action `(q • f)(x) = f(x q)` of
`ℤ[Q]` on `Additive (Q → X)`. Hence `g ↦ (c_g, ḡ)` is a homomorphism into the split metabelian
group `GroupRing.Affine ℤ Q (Additive (Q → X))`; it is injective when `Γ` is metabelian.

Main declarations:
* `instModuleTransl`: the translation module structure on `Additive (Q → X)`;
* `kkCocycle`, `kkCocycle_mul`, `kkHom`, `kkHom_injective`;
* `isAddTorsionFree_kkSpace`: the cocycle space is torsion-free when `Γ'` is.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

section Transl

variable (Q : Type*) [CommGroup Q] (X : Type*) [CommGroup X]

/-- Translation of functions on `Q` by `q`, as an additive endomorphism. -/
def translEnd (q : Q) : Additive (Q → X) →+ Additive (Q → X) where
  toFun f := Additive.ofMul fun x => Additive.toMul f (x * q)
  map_zero' := rfl
  map_add' _ _ := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.translEnd

/-- The translation action of `Q` on `Additive (Q → X)`. -/
def transl : Q →* AddMonoid.End (Additive (Q → X)) where
  toFun := translEnd Q X
  map_one' := AddMonoidHom.ext fun f =>
    congrArg Additive.ofMul (funext fun x => congrArg (Additive.toMul f) (mul_one x))
  map_mul' q q' := AddMonoidHom.ext fun f =>
    congrArg Additive.ofMul (funext fun x => congrArg (Additive.toMul f) (mul_assoc x q q').symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.transl

/-- The `ℤ[Q]`-module structure on `Additive (Q → X)` by translation. -/
instance instModuleTransl : Module (MonoidAlgebra ℤ Q) (Additive (Q → X)) :=
  Module.compHom (Additive (Q → X))
    (MonoidAlgebra.lift ℤ (AddMonoid.End (Additive (Q → X))) Q (transl Q X)).toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.instModuleTransl

variable {Q X}

theorem of_smul_transl (q : Q) (f : Additive (Q → X)) :
    MonoidAlgebra.of ℤ Q q • f = transl Q X q f :=
  DFunLike.congr_fun (MonoidAlgebra.lift_of (transl Q X) q) f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.of_smul_transl

end Transl

section Cocycle

variable {Γ : Type*} [Group Γ]

theorem abOf_surjective : Function.Surjective (Abelianization.of : Γ → Abelianization Γ) :=
  fun y => QuotientGroup.induction_on y fun a => ⟨a, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.abOf_surjective

variable (Γ) in
/-- A set-theoretic section of the abelianization map. -/
noncomputable def kkSection : Abelianization Γ → Γ :=
  Function.surjInv abOf_surjective

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkSection

theorem of_kkSection (x : Abelianization Γ) : Abelianization.of (kkSection Γ x) = x :=
  Function.surjInv_eq abOf_surjective x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.of_kkSection

theorem kkElt_mem (g : Γ) (x : Abelianization Γ) :
    kkSection Γ x * g * (kkSection Γ (x * Abelianization.of g))⁻¹ ∈ commutator Γ := by
  rw [← Abelianization.ker_of Γ, MonoidHom.mem_ker, map_mul, map_mul, map_inv, of_kkSection,
    of_kkSection, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkElt_mem

/-- The value `s x · g · s(x ḡ)⁻¹ ∈ Γ'` of the cocycle before abelianizing. -/
noncomputable def kkElt (g : Γ) (x : Abelianization Γ) : commutator Γ :=
  ⟨kkSection Γ x * g * (kkSection Γ (x * Abelianization.of g))⁻¹, kkElt_mem g x⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkElt

theorem kkElt_mul (g h : Γ) (x : Abelianization Γ) :
    kkElt (g * h) x = kkElt g x * kkElt h (x * Abelianization.of g) := by
  apply Subtype.ext
  show kkSection Γ x * (g * h) * (kkSection Γ (x * Abelianization.of (g * h)))⁻¹ =
    kkSection Γ x * g * (kkSection Γ (x * Abelianization.of g))⁻¹ *
      (kkSection Γ (x * Abelianization.of g) * h *
        (kkSection Γ (x * Abelianization.of g * Abelianization.of h))⁻¹)
  rw [map_mul]
  simp only [mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkElt_mul

variable (Γ) in
/-- The cocycle space `Additive (Γᵃᵇ → (Γ')ᵃᵇ)`, a `ℤ[Γᵃᵇ]`-module by translation. -/
abbrev KKSpace : Type _ := Additive (Abelianization Γ → Abelianization (commutator Γ))

/-- The Kaloujnine–Krasner cocycle `c_g`. -/
noncomputable def kkCocycle (g : Γ) : KKSpace Γ :=
  Additive.ofMul fun x => Abelianization.of (kkElt g x)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkCocycle

theorem kkCocycle_mul (g h : Γ) :
    kkCocycle (g * h) =
      kkCocycle g + MonoidAlgebra.of ℤ (Abelianization Γ) (Abelianization.of g) • kkCocycle h := by
  apply Additive.toMul.injective
  rw [of_smul_transl]
  funext x
  show Abelianization.of (kkElt (g * h) x) =
    Abelianization.of (kkElt g x) * Abelianization.of (kkElt h (x * Abelianization.of g))
  rw [kkElt_mul, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkCocycle_mul

variable (Γ) in
/-- The Kaloujnine–Krasner homomorphism `g ↦ (c_g, ḡ)`. -/
noncomputable def kkHom : Γ →* GroupRing.Affine ℤ (Abelianization Γ) (KKSpace Γ) :=
  MonoidHom.mk' (fun g => ⟨Multiplicative.ofAdd (kkCocycle g), Abelianization.of g⟩)
    fun g h => SemidirectProduct.ext (congrArg Multiplicative.ofAdd (kkCocycle_mul g h))
      (map_mul Abelianization.of g h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkHom

/-- In a metabelian group the abelianization map of `Γ'` is injective. -/
theorem eq_one_of_abOf_eq_one (hG : IsMetabelianGroup Γ) {a : commutator Γ}
    (ha : Abelianization.of a = 1) : a = 1 := by
  have h2 : a ∈ commutator (commutator Γ) := by
    rw [← Abelianization.ker_of (commutator Γ)]
    exact MonoidHom.mem_ker.mpr ha
  have h3 : (a : Γ) ∈ ⁅commutator Γ, commutator Γ⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_of_mem _ h2
  have hG' : ⁅commutator Γ, commutator Γ⁆ = ⊥ := hG
  rw [hG'] at h3
  exact Subtype.ext (Subgroup.mem_bot.mp h3)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eq_one_of_abOf_eq_one

/-- **The Kaloujnine–Krasner embedding.** For metabelian `Γ`, `kkHom Γ` is injective. -/
theorem kkHom_injective (hG : IsMetabelianGroup Γ) : Function.Injective (kkHom Γ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hr : Abelianization.of g = 1 := congrArg SemidirectProduct.right hg
  have h1 : Abelianization.of (kkElt g 1) = 1 :=
    congrArg (fun z : GroupRing.Affine ℤ (Abelianization Γ) (KKSpace Γ) =>
      Additive.toMul (Multiplicative.toAdd z.left) 1) hg
  have h3 : kkSection Γ 1 * g * (kkSection Γ (1 * Abelianization.of g))⁻¹ = 1 :=
    congrArg Subtype.val (eq_one_of_abOf_eq_one hG h1)
  rw [hr, mul_one, mul_inv_eq_one] at h3
  exact mul_left_cancel (h3.trans (mul_one _).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkHom_injective

/-- If `Γ` is metabelian with torsion-free `Γ'`, then `(Γ')ᵃᵇ` is torsion-free. -/
theorem isMulTorsionFree_abDerived (hG : IsMetabelianGroup Γ)
    (htf : ∀ x ∈ commutator Γ, ∀ n : ℕ, n ≠ 0 → x ^ n = 1 → x = 1) :
    IsMulTorsionFree (Abelianization (commutator Γ)) where
  pow_left_injective n hn a b hab := by
    obtain ⟨a', rfl⟩ := abOf_surjective a
    obtain ⟨b', rfl⟩ := abOf_surjective b
    have h1 : Abelianization.of ((a' * b'⁻¹) ^ n) = 1 := by
      rw [map_pow, map_mul, map_inv, mul_pow, inv_pow]
      exact mul_inv_eq_one.mpr hab
    have h2 : ((a' * b'⁻¹ : commutator Γ) : Γ) ^ n = 1 :=
      congrArg Subtype.val (eq_one_of_abOf_eq_one hG h1)
    have h4 : a' * b'⁻¹ = 1 := Subtype.ext (htf _ (a' * b'⁻¹).2 n hn h2)
    exact congrArg Abelianization.of (mul_inv_eq_one.mp h4)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isMulTorsionFree_abDerived

/-- The cocycle space is torsion-free when `Γ` is metabelian with torsion-free `Γ'`. -/
theorem isAddTorsionFree_kkSpace (hG : IsMetabelianGroup Γ)
    (htf : ∀ x ∈ commutator Γ, ∀ n : ℕ, n ≠ 0 → x ^ n = 1 → x = 1) :
    IsAddTorsionFree (KKSpace Γ) :=
  haveI := isMulTorsionFree_abDerived hG htf
  inferInstance

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isAddTorsionFree_kkSpace

end Cocycle

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
