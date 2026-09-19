import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Algebra.HNNFinitePresentation
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.GroupTheory.HNNBrittonCyclic

/-!
# `E`, the double HNN extension of the Fournier-Facio base

`non_mf_groups_exist.tex`, Section "A torsion-free group with full MF radical":

> Let `E` be the double HNN extension of `P` with stable letters `u₁, u₂` and
> `uᵢPuᵢ⁻¹ = Pᵢ`; it is finitely presented and torsion-free, and its Bass--Serre
> action makes it acylindrically hyperbolic by the tree criterion of
> Minasyan--Osin.

This module builds that group, from one printed datum: an injective
homomorphism `f : P × P × S →* P`, which is the printed subgroup
`P₁ × P₂ × S ≤ P`.  Its three factor maps are `factorOne`, `factorTwo`,
`factorSimple`.

`E` is `Double (factorOne f) (factorTwo f) _ _`, abbreviated `Skeleton f hf`;
each stable letter is the stable letter of one of the two HNN extensions
(`skeletonU₁`, `skeletonU₂`), and the printed relations `uᵢ P uᵢ⁻¹ = Pᵢ` are
`skeleton_conj_u₁` and `skeleton_conj_u₂`.

Finite presentation is `HNNFinitePresentation.isFinitelyPresented_hnnExtension`
applied twice — its finite-generation hypothesis on the associated subgroups
holds because the first is `⊤ ≤ P` and the second is an isomorphic copy of `P`
inside `E₁`.  Torsion-freeness is `HNNBritton.isPowerTorsionFree_hnn`, also
twice.  Acylindrical hyperbolicity is the cited Minasyan--Osin input and lives
in `Manuscript.NonMF.FournierFacioInput`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

/-! ## The three factors of `P₁ × P₂ × S`, as maps into `P` -/

section Factors

variable {P S : Type} [Group P] [Group S] (f : (P × P × S) →* P)

/-- `P₁ ≤ P`, as the map `p ↦ f(p, 1, 1)`. -/
def factorOne : P →* P := f.comp (MonoidHom.inl P (P × S))

/-- `P₂ ≤ P`, as the map `p ↦ f(1, p, 1)`. -/
def factorTwo : P →* P :=
  f.comp ((MonoidHom.inr P (P × S)).comp (MonoidHom.inl P S))

/-- `S ≤ P`, as the map `x ↦ f(1, 1, x)`. -/
def factorSimple : S →* P :=
  f.comp ((MonoidHom.inr P (P × S)).comp (MonoidHom.inr P S))

theorem factorOne_injective (hf : Function.Injective f) :
    Function.Injective (factorOne f) :=
  hf.comp fun _ _ hab => congrArg (fun x : P × P × S => x.1) hab

theorem factorTwo_injective (hf : Function.Injective f) :
    Function.Injective (factorTwo f) :=
  hf.comp fun _ _ hab => congrArg (fun x : P × P × S => x.2.1) hab

theorem factorSimple_injective (hf : Function.Injective f) :
    Function.Injective (factorSimple f) :=
  hf.comp fun _ _ hab => congrArg (fun x : P × P × S => x.2.2) hab

/-- **`[S, P₁] = 1` inside `P`.**  The manuscript's "Since `S` commutes with
`P₁`".  No injectivity is needed: distinct factors of a direct product
commute. -/
theorem factorSimple_commute_factorOne (x : S) (p : P) :
    Commute (factorSimple f x) (factorOne f p) := by
  have hc : Commute (((1 : P), (1 : P), x) : P × P × S)
      ((p, (1 : P), (1 : S)) : P × P × S) := by
    show (((1 : P), (1 : P), x) : P × P × S) * (p, (1 : P), (1 : S)) =
      (p, (1 : P), (1 : S)) * (((1 : P), (1 : P), x) : P × P × S)
    simp
  exact hc.map f

end Factors

/-! ## `E`, the double HNN extension of `P` -/

section Double

variable {P : Type} [Group P] (j₁ j₂ : P →* P)

/-- `φ₁ : P ≅ P₁`, in the associated-subgroup shape Mathlib's `HNNExtension`
consumes.  The first stable letter conjugates *all* of `P` into `P₁`, so the
first associated subgroup is `⊤`. -/
noncomputable def stageOneEquiv (h₁ : Function.Injective j₁) :
    (⊤ : Subgroup P) ≃* j₁.range :=
  Subgroup.topEquiv.trans (MonoidHom.ofInjective h₁)

/-- `E₁ = ⟨P, u₁ ∣ u₁ p u₁⁻¹ = j₁(p)⟩`, the first of the two HNN extensions. -/
abbrev StageOne (h₁ : Function.Injective j₁) : Type :=
  HNNExtension P ⊤ j₁.range (stageOneEquiv j₁ h₁)

theorem stageOneEquiv_coe (h₁ : Function.Injective j₁) (p : P) :
    ((stageOneEquiv j₁ h₁ ⟨p, Subgroup.mem_top p⟩ : j₁.range) : P) = j₁ p :=
  rfl

/-- The defining relation of the first stable letter. -/
theorem stageOne_conj (h₁ : Function.Injective j₁) (p : P) :
    (HNNExtension.t : StageOne j₁ h₁) * HNNExtension.of p *
        (HNNExtension.t : StageOne j₁ h₁)⁻¹
      = HNNExtension.of (j₁ p) := by
  have h := HNNExtension.equiv_eq_conj (φ := stageOneEquiv j₁ h₁)
    (⟨p, Subgroup.mem_top p⟩ : (⊤ : Subgroup P))
  rw [stageOneEquiv_coe] at h
  exact h.symm

/-- The base copy of `P` inside `E₁`: the first associated subgroup of the
second HNN extension. -/
noncomputable abbrev stageOneBase (h₁ : Function.Injective j₁) :
    Subgroup (StageOne j₁ h₁) :=
  (HNNExtension.of : P →* StageOne j₁ h₁).range

/-- The copy of `P₂` inside `E₁`: the second associated subgroup. -/
noncomputable abbrev stageTwoTarget (h₁ : Function.Injective j₁) :
    Subgroup (StageOne j₁ h₁) :=
  j₂.range.map (HNNExtension.of : P →* StageOne j₁ h₁)

/-- `φ₂ : P ≅ P₂`, transported into `E₁`. -/
noncomputable def stageTwoEquiv (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) :
    stageOneBase j₁ h₁ ≃* stageTwoTarget j₁ j₂ h₁ :=
  (MonoidHom.ofInjective
      (HNNExtension.of_injective (φ := stageOneEquiv j₁ h₁))).symm.trans
    ((MonoidHom.ofInjective h₂).trans
      (Subgroup.equivMapOfInjective j₂.range
        (HNNExtension.of : P →* StageOne j₁ h₁)
        (HNNExtension.of_injective (φ := stageOneEquiv j₁ h₁))))

theorem stageTwoEquiv_coe (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) (p : P) :
    ((stageTwoEquiv j₁ j₂ h₁ h₂
        ⟨(HNNExtension.of p : StageOne j₁ h₁), ⟨p, rfl⟩⟩ :
          stageTwoTarget j₁ j₂ h₁) : StageOne j₁ h₁)
      = HNNExtension.of (j₂ p) := by
  have hsymm : (MonoidHom.ofInjective
      (HNNExtension.of_injective (φ := stageOneEquiv j₁ h₁))).symm
        ⟨(HNNExtension.of p : StageOne j₁ h₁), ⟨p, rfl⟩⟩ = p := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  simp only [stageTwoEquiv, MulEquiv.trans_apply, hsymm,
    Subgroup.coe_equivMapOfInjective_apply, MonoidHom.ofInjective_apply]

/-- **`E`, the double HNN extension of `P` with stable letters `u₁, u₂` and
`uᵢ P uᵢ⁻¹ = Pᵢ`.** -/
abbrev Double (h₁ : Function.Injective j₁) (h₂ : Function.Injective j₂) : Type :=
  HNNExtension (StageOne j₁ h₁) (stageOneBase j₁ h₁) (stageTwoTarget j₁ j₂ h₁)
    (stageTwoEquiv j₁ j₂ h₁ h₂)

/-- The embedding of the base `P` into `E`. -/
noncomputable def doubleIota (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) :
    P →* Double j₁ j₂ h₁ h₂ :=
  (HNNExtension.of : StageOne j₁ h₁ →* Double j₁ j₂ h₁ h₂).comp
    (HNNExtension.of : P →* StageOne j₁ h₁)

theorem doubleIota_injective (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) :
    Function.Injective (doubleIota j₁ j₂ h₁ h₂) := by
  intro a b hab
  have hab' : (HNNExtension.of (HNNExtension.of a) : Double j₁ j₂ h₁ h₂)
      = HNNExtension.of (HNNExtension.of b) := hab
  exact HNNExtension.of_injective (φ := stageOneEquiv j₁ h₁)
    (HNNExtension.of_injective (φ := stageTwoEquiv j₁ j₂ h₁ h₂) hab')

/-- `u₁`, the first stable letter, seen inside `E`. -/
noncomputable def firstStableLetter (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) : Double j₁ j₂ h₁ h₂ :=
  (HNNExtension.of : StageOne j₁ h₁ →* Double j₁ j₂ h₁ h₂) HNNExtension.t

/-- `u₂`, the second stable letter. -/
noncomputable def secondStableLetter (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) : Double j₁ j₂ h₁ h₂ :=
  HNNExtension.t

/-- `u₁ P u₁⁻¹ = P₁`. -/
theorem conj_firstStableLetter (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) (p : P) :
    firstStableLetter j₁ j₂ h₁ h₂ * doubleIota j₁ j₂ h₁ h₂ p *
        (firstStableLetter j₁ j₂ h₁ h₂)⁻¹
      = doubleIota j₁ j₂ h₁ h₂ (j₁ p) := by
  have h := stageOne_conj j₁ h₁ p
  show (HNNExtension.of : StageOne j₁ h₁ →* Double j₁ j₂ h₁ h₂) HNNExtension.t *
      (HNNExtension.of : StageOne j₁ h₁ →* Double j₁ j₂ h₁ h₂)
        (HNNExtension.of p) *
      ((HNNExtension.of : StageOne j₁ h₁ →* Double j₁ j₂ h₁ h₂)
        HNNExtension.t)⁻¹
    = (HNNExtension.of : StageOne j₁ h₁ →* Double j₁ j₂ h₁ h₂)
        (HNNExtension.of (j₁ p))
  rw [← map_inv, ← map_mul, ← map_mul, h]

/-- `u₂ P u₂⁻¹ = P₂`. -/
theorem conj_secondStableLetter (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) (p : P) :
    secondStableLetter j₁ j₂ h₁ h₂ * doubleIota j₁ j₂ h₁ h₂ p *
        (secondStableLetter j₁ j₂ h₁ h₂)⁻¹
      = doubleIota j₁ j₂ h₁ h₂ (j₂ p) := by
  have h := HNNExtension.equiv_eq_conj (φ := stageTwoEquiv j₁ j₂ h₁ h₂)
    (⟨(HNNExtension.of p : StageOne j₁ h₁), ⟨p, rfl⟩⟩ : stageOneBase j₁ h₁)
  rw [stageTwoEquiv_coe] at h
  exact h.symm

/-- **`E` is finitely presented.**  Both associated subgroups are finitely
generated: the first is `⊤` in the finitely presented group `P`, the second is
an isomorphic copy of `P` inside `E₁`. -/
theorem double_isFinitelyPresented (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) [Group.IsFinitelyPresented P] :
    Group.IsFinitelyPresented (Double j₁ j₂ h₁ h₂) := by
  haveI : Group.FG P := ProductFinitePresentation.fg_of_isFinitelyPresented P
  haveI : Group.FG ((⊤ : Subgroup P)) :=
    Group.fg_of_surjective (f := (Subgroup.topEquiv (G := P)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := P)).symm.surjective
  haveI : Group.IsFinitelyPresented (StageOne j₁ h₁) :=
    HNNFinitePresentation.isFinitelyPresented_hnnExtension (stageOneEquiv j₁ h₁)
  have hof : Function.Injective (HNNExtension.of : P → StageOne j₁ h₁) :=
    HNNExtension.of_injective (φ := stageOneEquiv j₁ h₁)
  haveI : Group.FG (stageOneBase j₁ h₁) :=
    Group.fg_of_surjective (f := (MonoidHom.ofInjective hof).toMonoidHom)
      (MonoidHom.ofInjective hof).surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension
    (stageTwoEquiv j₁ j₂ h₁ h₂)

/-- **`E` is torsion-free.**  An HNN extension of a torsion-free group is
torsion-free, applied twice. -/
theorem double_torsionFree (h₁ : Function.Injective j₁)
    (h₂ : Function.Injective j₂) (hP : IsPowerTorsionFree P) :
    IsPowerTorsionFree (Double j₁ j₂ h₁ h₂) :=
  HNNBritton.isPowerTorsionFree_hnn (stageTwoEquiv j₁ j₂ h₁ h₂)
    (HNNBritton.isPowerTorsionFree_hnn (stageOneEquiv j₁ h₁) hP)

end Double

/-! ## `E` at the printed data: one embedding `P × P × S ↪ P` -/

section Skeleton

variable {P S : Type} [Group P] [Group S] (f : (P × P × S) →* P)
    (hf : Function.Injective f)

/-- **The manuscript's `E`.**  The double HNN extension of `P` whose stable
letters conjugate `P` onto the two `P`-factors of the printed subgroup
`P₁ × P₂ × S ≤ P`. -/
abbrev Skeleton : Type :=
  Double (factorOne f) (factorTwo f) (factorOne_injective f hf)
    (factorTwo_injective f hf)

/-- `ι : P → E`. -/
noncomputable def skeletonIota : P →* Skeleton f hf :=
  doubleIota (factorOne f) (factorTwo f) (factorOne_injective f hf)
    (factorTwo_injective f hf)

/-- `u₁ ∈ E`. -/
noncomputable def skeletonU₁ : Skeleton f hf :=
  firstStableLetter (factorOne f) (factorTwo f) (factorOne_injective f hf)
    (factorTwo_injective f hf)

/-- `u₂ ∈ E`. -/
noncomputable def skeletonU₂ : Skeleton f hf :=
  secondStableLetter (factorOne f) (factorTwo f) (factorOne_injective f hf)
    (factorTwo_injective f hf)

theorem skeletonIota_injective : Function.Injective (skeletonIota f hf) :=
  doubleIota_injective _ _ _ _

/-- `u₁ P u₁⁻¹ = P₁`. -/
theorem skeleton_conj_u₁ (p : P) :
    skeletonU₁ f hf * skeletonIota f hf p * (skeletonU₁ f hf)⁻¹
      = skeletonIota f hf (factorOne f p) :=
  conj_firstStableLetter _ _ _ _ p

/-- `u₂ P u₂⁻¹ = P₂`. -/
theorem skeleton_conj_u₂ (p : P) :
    skeletonU₂ f hf * skeletonIota f hf p * (skeletonU₂ f hf)⁻¹
      = skeletonIota f hf (factorTwo f p) :=
  conj_secondStableLetter _ _ _ _ p

theorem skeleton_isFinitelyPresented [Group.IsFinitelyPresented P] :
    Group.IsFinitelyPresented (Skeleton f hf) :=
  double_isFinitelyPresented _ _ _ _

theorem skeleton_torsionFree (hP : IsPowerTorsionFree P) :
    IsPowerTorsionFree (Skeleton f hf) :=
  double_torsionFree _ _ _ _ hP

end Skeleton

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
