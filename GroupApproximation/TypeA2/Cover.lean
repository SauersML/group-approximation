import Mathlib.Algebra.Group.Action.Hom
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Subgroup.Centralizer
import GroupApproximation.TypeA2.Extension

/-!
# Normalizer covers of permutation groups

Let `Γ ≤ Sym(X)` and let `φ : H →* Sym(X)` take values in the normalizer of `Γ`.  Conjugation by
`φ h` is an automorphism of `Γ` (`coverConj`), and `Γ ⋊ H` acts on `X` by `(γ, h) · x = γ (φ h x)`
(`coverAction`).  A subset `S` preserved by `Γ` and by `φ` is a sub-action (`coverSubMulAction`).

`isTypeA2_cover`: if `Γ` and `H` are finitely presented, the point stabilizers of `Γ` on `S` are
finitely generated and `Γ` has finitely many orbits on `S × S`, the action `Γ ⋊ H ↷ S` is of
type [A₂].  This is `isTypeA2_of_exact` for `Γ →inl Γ ⋊ H →right H`.
-/

open MulAction

namespace GroupApproximation.TypeA2

section Cover

variable {X : Type*} (Γ : Subgroup (Equiv.Perm X)) {H : Type*} [Group H]
  (φ : H →* Equiv.Perm X) (hφ : ∀ h, φ h ∈ Subgroup.normalizer (Γ : Set (Equiv.Perm X)))

/-- Conjugation by `φ h`, as an automorphism of `Γ`. -/
def coverConj : H →* MulAut Γ :=
  Γ.normalizerMonoidHom.comp (φ.codRestrict (Subgroup.normalizer (Γ : Set (Equiv.Perm X))) hφ)

theorem coverConj_apply_coe (h : H) (γ : Γ) :
    ((coverConj Γ φ hφ h γ : Γ) : Equiv.Perm X) = φ h * γ * (φ h)⁻¹ :=
  rfl

/-- The permutation representation `(γ, h) ↦ γ ∘ φ h` of `Γ ⋊ H`. -/
def coverHom : Γ ⋊[coverConj Γ φ hφ] H →* Equiv.Perm X :=
  SemidirectProduct.lift Γ.subtype φ fun _ => by
    ext γ x
    rfl

theorem coverHom_apply (p : Γ ⋊[coverConj Γ φ hφ] H) (x : X) :
    coverHom Γ φ hφ p x = (p.left : Equiv.Perm X) (φ p.right x) :=
  rfl

/-- The action of `Γ ⋊ H` on `X`: `(γ, h) · x = γ (φ h x)`. -/
instance coverAction : MulAction (Γ ⋊[coverConj Γ φ hφ] H) X :=
  MulAction.compHom X (coverHom Γ φ hφ)

theorem cover_smul_def (p : Γ ⋊[coverConj Γ φ hφ] H) (x : X) :
    p • x = (p.left : Equiv.Perm X) (φ p.right x) :=
  rfl

/-- A subset preserved by `Γ` and by `φ`, as a sub-action of `Γ ⋊ H ↷ X`. -/
def coverSubMulAction (S : Set X) (hΓS : ∀ γ ∈ Γ, ∀ x ∈ S, γ x ∈ S)
    (hφS : ∀ h, ∀ x ∈ S, φ h x ∈ S) : SubMulAction (Γ ⋊[coverConj Γ φ hφ] H) X where
  carrier := S
  smul_mem' := fun p {x} hx => hΓS _ p.left.2 _ (hφS p.right x hx)

variable {Γ φ hφ}

theorem mem_coverSubMulAction {S : Set X} {hΓS : ∀ γ ∈ Γ, ∀ x ∈ S, γ x ∈ S}
    {hφS : ∀ h, ∀ x ∈ S, φ h x ∈ S} {x : X} :
    x ∈ coverSubMulAction Γ φ hφ S hΓS hφS ↔ x ∈ S :=
  Iff.rfl

theorem coverSubMulAction_coe_smul {S : Set X} {hΓS : ∀ γ ∈ Γ, ∀ x ∈ S, γ x ∈ S}
    {hφS : ∀ h, ∀ x ∈ S, φ h x ∈ S} (p : Γ ⋊[coverConj Γ φ hφ] H)
    (s : coverSubMulAction Γ φ hφ S hΓS hφS) :
    ((p • s : coverSubMulAction Γ φ hφ S hΓS hφS) : X) = (p.left : Equiv.Perm X) (φ p.right s) :=
  rfl

end Cover

/-- **Normalizer covers are of type [A₂].**  Let `Γ ≤ Sym(X)` and `H` be finitely presented, let
`φ : H →* Sym(X)` take values in the normalizer of `Γ`, and let `S` be a non-empty subset preserved
by `Γ` and by `φ`.  If `Γ` has finitely generated point stabilizers at the points of `S` and
finitely many orbits on `S × S`, then `Γ ⋊ H ↷ S` is of type [A₂]. -/
theorem isTypeA2_cover {X H : Type} (Γ : Subgroup (Equiv.Perm X)) [Group H]
    (φ : H →* Equiv.Perm X) (hφ : ∀ h, φ h ∈ Subgroup.normalizer (Γ : Set (Equiv.Perm X)))
    [Group.IsFinitelyPresented Γ] [Group.IsFinitelyPresented H] (S : Set X)
    (hΓS : ∀ γ ∈ Γ, ∀ x ∈ S, γ x ∈ S) (hφS : ∀ h, ∀ x ∈ S, φ h x ∈ S) (hne : S.Nonempty)
    (hstab : ∀ x ∈ S, (stabilizer Γ x).FG)
    (horb : ∃ F : Finset (X × X), ∀ x ∈ S, ∀ y ∈ S, ∃ f ∈ F, ∃ γ ∈ Γ, γ f.1 = x ∧ γ f.2 = y) :
    IsTypeA2 (Γ ⋊[coverConj Γ φ hφ] H) (coverSubMulAction Γ φ hφ S hΓS hφS) := by
  letI : MulAction Γ (coverSubMulAction Γ φ hφ S hΓS hφS) :=
    MulAction.compHom _ (SemidirectProduct.inl : Γ →* Γ ⋊[coverConj Γ φ hφ] H)
  have hinl : ∀ (γ : Γ) (s : coverSubMulAction Γ φ hφ S hΓS hφS),
      ((γ • s : coverSubMulAction Γ φ hφ S hΓS hφS) : X) = (γ : Equiv.Perm X) s := by
    intro γ s
    show (γ : Equiv.Perm X) (φ 1 s) = (γ : Equiv.Perm X) s
    rw [map_one, Equiv.Perm.one_apply]
  have hstabeq : ∀ s : coverSubMulAction Γ φ hφ S hΓS hφS,
      stabilizer Γ s = stabilizer Γ (s : X) := by
    intro s
    ext γ
    simp only [mem_stabilizer_iff]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [hinl] at h'
      exact h'
    · intro h
      exact Subtype.ext ((hinl γ s).trans h)
  have hΓ : IsTypeA2 Γ (coverSubMulAction Γ φ hφ S hΓS hφS) := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨⟨⟨x, hx⟩⟩, inferInstance, fun s => ?_, ?_⟩
    · rw [hstabeq]
      exact hstab s s.2
    · obtain ⟨F, hF⟩ := horb
      refine finite_orbitRel_quotient_iff.mpr
        ⟨F.preimage (fun q : coverSubMulAction Γ φ hφ S hΓS hφS ×
          coverSubMulAction Γ φ hφ S hΓS hφS => ((q.1 : X), (q.2 : X))) ?_, ?_⟩
      · intro a _ b _ hab
        exact Prod.ext (Subtype.ext (congrArg Prod.fst hab)) (Subtype.ext (congrArg Prod.snd hab))
      · rintro ⟨s, t⟩
        obtain ⟨f, hf, γ, hγ, hγ1, hγ2⟩ := hF s s.2 t t.2
        have hback : ∀ z : X, γ z ∈ S → z ∈ S := fun z hz => by
          have h := hΓS γ⁻¹ (inv_mem hγ) _ hz
          rwa [show (γ⁻¹ : Equiv.Perm X) (γ z) = z from Equiv.symm_apply_apply γ z] at h
        have h1 : f.1 ∈ S := hback f.1 (by rw [hγ1]; exact s.2)
        have h2 : f.2 ∈ S := hback f.2 (by rw [hγ2]; exact t.2)
        refine ⟨(⟨f.1, h1⟩, ⟨f.2, h2⟩), Finset.mem_preimage.mpr hf, ⟨γ, hγ⟩, ?_⟩
        exact Prod.ext (Subtype.ext ((hinl ⟨γ, hγ⟩ _).trans hγ1))
          (Subtype.ext ((hinl ⟨γ, hγ⟩ _).trans hγ2))
  exact isTypeA2_of_exact SemidirectProduct.inl SemidirectProduct.rightHom
    SemidirectProduct.inl_injective SemidirectProduct.rightHom_surjective
    SemidirectProduct.range_inl_eq_ker_rightHom.symm (fun _ _ => rfl) hΓ

end GroupApproximation.TypeA2
