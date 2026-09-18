import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetActionSemisplit
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetTransfer
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StableFunctor

/-!
# The Kasparov-product action on `Ext(-, J)` from a Cuntz-picture zigzag

Lane `TWWSch3d3-3A`, work order `WO-TWWSchafhauser-3d3-3A`. The manuscript statement is
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). It cites
Tikuisis--White--Winter through C. Schafhauser, J. reine angew. Math. 759 (2020), §§4--5.
Rosenberg and Schochet move the vanishing of the boundary maps along a `KK`-equivalence. For
this, `Ext(-, J) = KK¹(-, J)` must be a module over the Kasparov product (Blackadar 18.5, 18.7.1).

In Cuntz's picture a class `x ∈ KK(A, B)` is a homotopy class of `⋆`-homomorphisms
`f : F A → F B` with `F A = 𝒦 ⊗ qA` (J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987)). This
file is the formal part. It takes a stabilized homotopy functor `F` and a zigzag
`A ←p— M A —c→ F A`, natural in `A` (in the model, `M A = qA`, `p = π_A` and `c` is the corner
embedding). It also takes four properties of the semisplit group `ExtSS = Ext⁻¹`:

* every Busby cycle of an algebra in the class `P` is semisplit (Choi--Effros for nuclear `A`);
* `p^*` and `c^*` are bijective on `ExtSS (-) J` (Cuntz; stability);
* `ExtSS.comap` is invariant under homotopy on the objects `F A` (Kasparov 1980, §7).

The identification `e_A : Ext(A, J) ≅ ExtSS(F A, J)` is `(c^*)⁻¹ ∘ p^* ∘ ε⁻¹`, where `ε` is the
forgetful isomorphism. The action is `x^* = e_A⁻¹ ∘ f^* ∘ e_B`.

* `ExtSSCuntzData.act_comp`, `act_id`: the action turns composition into composition.
* `ExtSSCuntzData.act_classOf`: the class of a unital `⋆`-homomorphism acts by `ExtGroup.comap`.
* `ExtSSCuntzData.toExtKKAction`: the resulting `ExtKKAction F.toKasparovTheory P J`.
* `ExtSSCuntzData.act_spec`: the defining property for an arbitrary class `x`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

section Assembly

variable (F : TWWKK.StableFunctor) (P : SepCStarAlgebra.{0} → Prop)
variable (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **Cuntz-picture data for the action of `F.toKasparovTheory` on `Ext(-, J)`.**
A natural zigzag `A ←p— M A —c→ F A` together with the four properties of `ExtSS` that the
construction uses. In the model `F A = 𝒦 ⊗ qA`, `M A = qA`, `p = π_A` and `c` is the corner
embedding. -/
structure ExtSSCuntzData where
  /-- The middle object of the zigzag (in the model, `qA`). -/
  M : SepCStarAlgebra.{0} → Type
  /-- The middle objects are non-unital C⋆-algebras. -/
  [instM : ∀ A : SepCStarAlgebra.{0}, NonUnitalCStarAlgebra (M A)]
  /-- Functoriality of the middle object. -/
  mapM : ∀ {A B : SepCStarAlgebra.{0}}, (A →⋆ₐ[ℂ] B) → (M A →⋆ₙₐ[ℂ] M B)
  /-- The left leg `M A → A` (in the model, `π_A : qA → A`). -/
  p : ∀ A : SepCStarAlgebra.{0}, M A →⋆ₙₐ[ℂ] A
  /-- The right leg `M A → F A` (in the model, the corner `qA → 𝒦 ⊗ qA`). -/
  c : ∀ A : SepCStarAlgebra.{0}, M A →⋆ₙₐ[ℂ] F.obj A
  /-- Naturality of the left leg. -/
  p_natural : ∀ {A B : SepCStarAlgebra.{0}} (φ : A →⋆ₐ[ℂ] B),
    (φ : A →⋆ₙₐ[ℂ] B).comp (p A) = (p B).comp (mapM φ)
  /-- Naturality of the right leg. -/
  c_natural : ∀ {A B : SepCStarAlgebra.{0}} (φ : A →⋆ₐ[ℂ] B),
    (F.map φ).comp (c A) = (c B).comp (mapM φ)
  /-- Every Busby cycle of an algebra in `P` is semisplit (Choi--Effros). -/
  semisplit : ∀ {A : SepCStarAlgebra.{0}}, P A → ∀ x : BusbyCycle A J, x.IsSemisplit
  /-- `p^*` is bijective on `Ext⁻¹(-, J)` (Cuntz). -/
  p_bijective : ∀ A : SepCStarAlgebra.{0},
    Function.Bijective (ExtSS.comap (p A) : ExtSS A J →+ ExtSS (M A) J)
  /-- `c^*` is bijective on `Ext⁻¹(-, J)` (stability). -/
  c_bijective : ∀ A : SepCStarAlgebra.{0},
    Function.Bijective (ExtSS.comap (c A) : ExtSS (F.obj A) J →+ ExtSS (M A) J)
  /-- `Ext⁻¹(-, J)` is homotopy invariant on the objects `F A` (Kasparov). -/
  homotopy : ∀ {A B : SepCStarAlgebra.{0}} {f g : F.obj A →⋆ₙₐ[ℂ] F.obj B},
    TWWKK.NHomotopic f g →
      (ExtSS.comap f : ExtSS (F.obj B) J →+ ExtSS (F.obj A) J) = ExtSS.comap g

attribute [instance] ExtSSCuntzData.instM

variable {F P J}

namespace ExtSSCuntzData

variable (D : ExtSSCuntzData F P J)
variable {A B C : SepCStarAlgebra.{0}}

/-- The forgetful isomorphism `ε_A : Ext⁻¹(A, J) ≅ Ext(A, J)` for `A` in `P`. -/
noncomputable def epsEquiv (hA : P A) : ExtSS A J ≃+ ExtGroup A J :=
  ExtSS.toExtEquiv (D.semisplit hA)

/-- `p^* : Ext⁻¹(A, J) ≅ Ext⁻¹(M A, J)`. -/
noncomputable def piEquiv (A : SepCStarAlgebra.{0}) : ExtSS A J ≃+ ExtSS (D.M A) J :=
  AddEquiv.ofBijective (ExtSS.comap (D.p A) : ExtSS A J →+ ExtSS (D.M A) J) (D.p_bijective A)

/-- `c^* : Ext⁻¹(F A, J) ≅ Ext⁻¹(M A, J)`. -/
noncomputable def kapEquiv (A : SepCStarAlgebra.{0}) : ExtSS (F.obj A) J ≃+ ExtSS (D.M A) J :=
  AddEquiv.ofBijective (ExtSS.comap (D.c A) : ExtSS (F.obj A) J →+ ExtSS (D.M A) J)
    (D.c_bijective A)

/-- **The identification** `e_A = (c^*)⁻¹ ∘ p^* ∘ ε_A⁻¹ : Ext(A, J) ≅ Ext⁻¹(F A, J)`. -/
noncomputable def eEquiv (hA : P A) : ExtGroup A J ≃+ ExtSS (F.obj A) J :=
  ((D.epsEquiv hA).symm.trans (D.piEquiv A)).trans (D.kapEquiv A).symm

theorem epsEquiv_apply (hA : P A) (ζ : ExtSS A J) : D.epsEquiv hA ζ = ExtSS.toExt ζ :=
  rfl

/-- `toExt (ε_A⁻¹ ξ) = ξ`. -/
theorem toExt_epsEquiv_symm (hA : P A) (ξ : ExtGroup A J) :
    ExtSS.toExt ((D.epsEquiv hA).symm ξ) = ξ :=
  (D.epsEquiv hA).apply_symm_apply ξ

/-- **The defining property of `e_A`**: `c^* (e_A ξ) = p^* (ε_A⁻¹ ξ)`. -/
theorem c_eEquiv (hA : P A) (ξ : ExtGroup A J) :
    ExtSS.comap (D.c A) (D.eEquiv hA ξ) = ExtSS.comap (D.p A) ((D.epsEquiv hA).symm ξ) :=
  (D.kapEquiv A).apply_symm_apply (D.piEquiv A ((D.epsEquiv hA).symm ξ))

/-- `ε⁻¹` is natural. -/
theorem epsEquiv_symm_comap (hA : P A) (hB : P B) (φ : A →⋆ₐ[ℂ] B) (ξ : ExtGroup B J) :
    (D.epsEquiv hA).symm (ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) ξ) =
      ExtSS.comap (φ : A →⋆ₙₐ[ℂ] B) ((D.epsEquiv hB).symm ξ) := by
  apply (D.epsEquiv hA).injective
  rw [AddEquiv.apply_symm_apply, D.epsEquiv_apply hA, ExtSS.toExt_comap_apply,
    D.toExt_epsEquiv_symm hB]

/-- **Naturality of `e`** along a unital `⋆`-homomorphism `φ : A → B`:
`(F φ)^* ∘ e_B = e_A ∘ φ^*`. -/
theorem e_natural (hA : P A) (hB : P B) (φ : A →⋆ₐ[ℂ] B) (ξ : ExtGroup B J) :
    ExtSS.comap (F.map φ) (D.eEquiv hB ξ) =
      D.eEquiv hA (ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) ξ) := by
  apply (D.c_bijective A).1
  calc ExtSS.comap (D.c A) (ExtSS.comap (F.map φ) (D.eEquiv hB ξ))
      = ExtSS.comap ((F.map φ).comp (D.c A)) (D.eEquiv hB ξ) :=
        (ExtSS.comap_comp_apply (F.map φ) (D.c A) _).symm
    _ = ExtSS.comap ((D.c B).comp (D.mapM φ)) (D.eEquiv hB ξ) := by rw [D.c_natural φ]
    _ = ExtSS.comap (D.mapM φ) (ExtSS.comap (D.c B) (D.eEquiv hB ξ)) :=
        ExtSS.comap_comp_apply (D.c B) (D.mapM φ) _
    _ = ExtSS.comap (D.mapM φ) (ExtSS.comap (D.p B) ((D.epsEquiv hB).symm ξ)) := by
        rw [D.c_eEquiv hB ξ]
    _ = ExtSS.comap ((D.p B).comp (D.mapM φ)) ((D.epsEquiv hB).symm ξ) :=
        (ExtSS.comap_comp_apply (D.p B) (D.mapM φ) _).symm
    _ = ExtSS.comap ((φ : A →⋆ₙₐ[ℂ] B).comp (D.p A)) ((D.epsEquiv hB).symm ξ) := by
        rw [D.p_natural φ]
    _ = ExtSS.comap (D.p A) (ExtSS.comap (φ : A →⋆ₙₐ[ℂ] B) ((D.epsEquiv hB).symm ξ)) :=
        ExtSS.comap_comp_apply (φ : A →⋆ₙₐ[ℂ] B) (D.p A) _
    _ = ExtSS.comap (D.p A) ((D.epsEquiv hA).symm (ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) ξ)) := by
        rw [D.epsEquiv_symm_comap hA hB φ ξ]
    _ = ExtSS.comap (D.c A) (D.eEquiv hA (ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) ξ)) :=
        (D.c_eEquiv hA _).symm

/-! ### The action of homotopy classes -/

/-- The pull-back `f^* : Ext⁻¹(F B, J) → Ext⁻¹(F A, J)` of a homotopy class `[f]`. It is well
defined by homotopy invariance. -/
def pullClass (x : TWWKK.HomotopyClass (F.obj A) (F.obj B)) :
    ExtSS (F.obj B) J →+ ExtSS (F.obj A) J :=
  Quot.lift (fun f : F.obj A →⋆ₙₐ[ℂ] F.obj B => (ExtSS.comap f : ExtSS (F.obj B) J →+ _))
    (fun _ _ h => D.homotopy h) x

theorem pullClass_mk (f : F.obj A →⋆ₙₐ[ℂ] F.obj B) :
    D.pullClass (TWWKK.HomotopyClass.mk f) = ExtSS.comap f :=
  rfl

/-- Every class is pulled back by one of its representatives. -/
theorem exists_pullClass_eq (x : TWWKK.HomotopyClass (F.obj A) (F.obj B)) :
    ∃ f : F.obj A →⋆ₙₐ[ℂ] F.obj B,
      x = TWWKK.HomotopyClass.mk f ∧ D.pullClass x = ExtSS.comap f := by
  obtain ⟨f, rfl⟩ := Quot.exists_rep x
  exact ⟨f, rfl, rfl⟩

theorem pullClass_comp (y : TWWKK.HomotopyClass (F.obj B) (F.obj C))
    (x : TWWKK.HomotopyClass (F.obj A) (F.obj B)) :
    D.pullClass (TWWKK.HomotopyClass.comp y x) = (D.pullClass x).comp (D.pullClass y) := by
  induction x using TWWKK.HomotopyClass.ind with
  | mk f =>
    induction y using TWWKK.HomotopyClass.ind with
    | mk g => exact ExtSS.comap_comp g f

/-- **The action** of `x = [f] ∈ [F A, F B]`: `x^* = e_A⁻¹ ∘ f^* ∘ e_B`. -/
noncomputable def act (hA : P A) (hB : P B) (x : TWWKK.HomotopyClass (F.obj A) (F.obj B)) :
    ExtGroup B J →+ ExtGroup A J :=
  (D.eEquiv hA).symm.toAddMonoidHom.comp ((D.pullClass x).comp (D.eEquiv hB).toAddMonoidHom)

theorem act_apply (hA : P A) (hB : P B) (x : TWWKK.HomotopyClass (F.obj A) (F.obj B))
    (ξ : ExtGroup B J) : D.act hA hB x ξ = (D.eEquiv hA).symm (D.pullClass x (D.eEquiv hB ξ)) :=
  rfl

/-- **The defining property of the action**, for an arbitrary class `x`:
`p^* (ε_A⁻¹ (x^* ξ)) = c^* (f^* (e_B ξ))`. -/
theorem act_spec (hA : P A) (hB : P B) (x : TWWKK.HomotopyClass (F.obj A) (F.obj B))
    (ξ : ExtGroup B J) :
    ExtSS.comap (D.p A) ((D.epsEquiv hA).symm (D.act hA hB x ξ)) =
      ExtSS.comap (D.c A) (D.pullClass x (D.eEquiv hB ξ)) := by
  rw [← D.c_eEquiv hA, D.act_apply, AddEquiv.apply_symm_apply]

/-- The action of a composite is the composite of the actions. -/
theorem act_comp (hA : P A) (hB : P B) (hC : P C)
    (x : TWWKK.HomotopyClass (F.obj A) (F.obj B)) (y : TWWKK.HomotopyClass (F.obj B) (F.obj C))
    (ξ : ExtGroup C J) :
    D.act hA hC (TWWKK.HomotopyClass.comp y x) ξ = D.act hA hB x (D.act hB hC y ξ) := by
  rw [D.act_apply, D.act_apply, D.act_apply, D.pullClass_comp, AddMonoidHom.comp_apply,
    AddEquiv.apply_symm_apply]

/-- The identity class acts as the identity. -/
theorem act_id (hA : P A) (ξ : ExtGroup A J) :
    D.act hA hA (TWWKK.HomotopyClass.id (F.obj A)) ξ = ξ := by
  show (D.eEquiv hA).symm (ExtSS.comap (NonUnitalStarAlgHom.id ℂ (F.obj A)) (D.eEquiv hA ξ)) = ξ
  rw [ExtSS.comap_id_apply, AddEquiv.symm_apply_apply]

/-- **The class of a unital `⋆`-homomorphism acts by pull-back**: `[F φ]^* = φ^*`. -/
theorem act_classOf (hA : P A) (hB : P B) (φ : A →⋆ₐ[ℂ] B) :
    D.act hA hB (TWWKK.HomotopyClass.mk (F.map φ)) = ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) := by
  refine AddMonoidHom.ext fun ξ => ?_
  rw [D.act_apply, D.pullClass_mk, D.e_natural hA hB φ ξ, AddEquiv.symm_apply_apply]

/-- **The action of `F.toKasparovTheory` on `Ext(-, J)`**, for any group structure on the
morphism sets. -/
noncomputable def toExtKKAction [∀ A B : SepCStarAlgebra.{0}, AddCommGroup (F.Hom A B)] :
    ExtKKAction F.toKasparovTheory P J where
  act hA hB x := D.act hA hB x
  act_product hA hB hC x y ξ := D.act_comp hA hB hC x y ξ
  act_unit hA ξ := D.act_id hA ξ

theorem toExtKKAction_act [∀ A B : SepCStarAlgebra.{0}, AddCommGroup (F.Hom A B)]
    (hA : P A) (hB : P B) (x : F.toKasparovTheory.Grp A B) :
    D.toExtKKAction.act hA hB x = D.act hA hB x :=
  rfl

/-- **`classOf φ` acts by `ExtGroup.comap φ`.** -/
theorem toExtKKAction_classOf [∀ A B : SepCStarAlgebra.{0}, AddCommGroup (F.Hom A B)]
    (hA : P A) (hB : P B) (φ : A →⋆ₐ[ℂ] B) :
    D.toExtKKAction.act hA hB (F.toKasparovTheory.classOf φ) =
      ExtGroup.comap (φ : A →⋆ₙₐ[ℂ] B) :=
  D.act_classOf hA hB φ

end ExtSSCuntzData

end Assembly

end GroupApproximation.Full.TWWSchafhauser
